-- Prove2me | Theorems.Thm_FluidGreedyMatching_CliqueBomb_certification
-- name    : FluidGreedyMatching.CliqueBomb.certification
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:58:35.477776+00:00
-- url     : https://prove2.me/theorems/12082c3b-007e-4160-a1ac-fbb1244c5d25
-- title:
--   Lemma 3.1 — Count-process certification
-- statement:
--   Run one fixed algorithm $A\in\{\mathrm{MRG},\mathrm{RDO}\}$ on finite graphs $G_n$ with $|V(G_n)|=O(n)$, freezing after termination. Let the adapted nonnegative integer count vector $Z_t$ have last coordinate $|M_t|$, satisfy a uniform $O(n)$ coordinate bound and $Z_0=nz_0+O(1)$, and recover the active vertex count as $n\,u(Z_t/n)$ for a fixed linear $u$. Let $h$ be a fixed linear budget.
--
--   Suppose $K,\beta>0$ are independent of $\varepsilon$. For every sufficiently small fixed $\varepsilon>0$, assume a bounded open box $D_\varepsilon$ contains $z_0$ and a Lipschitz log-time drift $g$ satisfies $u\ge c_\varepsilon>0$ there. Assume C1: the conditional increment law depends only on $Z_t$ and jumps are bounded by $\beta$ within this box. Assume C2:
--   $$\left\|\mathbb E[Z_{t+1}-Z_t\mid\mathcal F_t]-\frac{g(Z_t/n)}{u(Z_t/n)}\right\|_\infty\le\frac{C_\varepsilon}{n}.$$
--   Assume C3: the solution $\bar z'=g(\bar z)$ from $z_0$ first attains budget $\varepsilon$ at a finite positive time $s_\varepsilon$, stays in $D_\varepsilon$ through that time, and has budget greater than $\varepsilon$ before it. Assume C4: there is a Lipschitz $\Phi$ such that, for every deterministic step sequence $t_1(n)$, there are nonnegative sequences $e_n,p_n\to0$ for which, except on an event of probability at most $p_n$, closeness $\|Z_{t_1}/n-\bar z(s_\varepsilon)\|_\infty\le\varepsilon$ implies
--   $$\left||M|-|M_{t_1}|-n\Phi(Z_{t_1}/n)\right|\le K\varepsilon n+e_nn.$$
--   Write $\bar\mu$ for the last coordinate. If the following limit exists, then
--   $$\Lambda=\lim_{\varepsilon\downarrow0}\bigl(\bar\mu(s_\varepsilon)+\Phi(\bar z(s_\varepsilon))\bigr),\qquad
--   \frac{|M|}{n}\xrightarrow{\Pr}\Lambda,\qquad \frac{\mathbb E|M|}{n}\longrightarrow\Lambda.$$
--
--   This supplies both terminal limits from the four explicit conditions; none of the convergence conclusions is built into the process interface.
--
--   Differences from the source:
--   - encoding: positive sizes, matching run and nonnegative integer counts → size j+1, finite labeled graphs with the exact conditional step kernel, and real coordinates required to be natural numbers; reason: relabeling and embedding the counts into real vectors preserve every source run
--   - encoding: for every small epsilon the domain, drift, trajectory and end-phase function, with O and o terms → explicit epsilon-indexed auxiliary data and positive constants, and explicit nonnegative error and failure sequences tending to zero at fixed epsilon; reason: this exposes the quantifier scopes without imposing a joint epsilon-of-size limit; common auxiliary functions are included by constant families
--   - encoding: a bounded count vector and expected output matching size → an explicit uniform count bound and an integral of the terminal finite-state matching cardinality; reason: the finite-state output is measurable and bounded, so its expectation is integrable rather than a default-zero integral
-- source:
--   Sayan Mukherjee, Fluid Limits and Upper Bounds for Randomized Greedy Matching, STOC 2027 submission #492 (October 2026), Section 3.3 preamble and Lemma 3.1, p. 11; proof p. 12

import Mathlib
import Definitions.Def_FluidGreedyMatching_CliqueBomb_ProcessModel

set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology NNReal

namespace FluidGreedyMatching.CliqueBomb

/-- Lemma 3.1, p. 11, including the count-vector conventions in its section preamble.
The epsilon-dependent auxiliary data are not required to agree away from their own cutoff. -/
theorem certification {a : ℕ} (P : ProcessFamily (a + 1))
    (N : ℕ → ℕ) (G : (n : ℕ) → SimpleGraph (Fin (N n)))
    (rule : (n : ℕ) → NeighborRule (Fin (N n)))
    (hAlgorithm : (∀ n, rule n = none) ∨ (∀ n, ∃ o, rule n = some o))
    (run : (n : ℕ) → ℕ → P.space n → RunState (Fin (N n)))
    (hrun : isAlgorithmRun P N G rule run)
    (hvertices : ∃ B : ℝ, 0 < B ∧ ∀ᶠ n in atTop, (N n : ℝ) ≤ B * scale n)
    (hcounts : ∀ n t, ∀ᵐ ω ∂P.law n, ∀ i, ∃ k : ℕ, P.Z n t ω i = k)
    (hbounded : ∃ B : ℝ, 0 < B ∧ ∀ᶠ n in atTop,
      ∀ t, ∀ᵐ ω ∂P.law n, ‖P.Z n t ω‖ ≤ B * scale n)
    (hlast : ∀ n t, ∀ᵐ ω ∂P.law n,
      P.Z n t ω (Fin.last a) = ((run n t ω).2.card : ℝ))
    (u h : Vec (a + 1) →ₗ[ℝ] ℝ)
    (hactive : ∀ n t, ∀ᵐ ω ∂P.law n,
      scale n * u (normalized P n t ω) = ((run n t ω).1.card : ℝ))
    (hfreeze : ∀ n t, ∀ᵐ ω ∂P.law n, (run n t ω).1 = ∅ → P.Z n (t + 1) ω = P.Z n t ω)
    (z₀ : Vec (a + 1))
    (hinit : ∃ B : ℝ, 0 < B ∧ ∀ᶠ n in atTop,
      ∀ᵐ ω ∂P.law n, ‖P.Z n 0 ω - scale n • z₀‖ ≤ B)
    (K β ε₀ : ℝ) (hK : 0 < K) (hβ : 0 < β) (hε₀ : 0 < ε₀)
    (D : ℝ → Set (Vec (a + 1))) (g : ℝ → Vec (a + 1) → Vec (a + 1))
    (c C : ℝ → ℝ) (zbar : ℝ → ℝ → Vec (a + 1)) (sε : ℝ → ℝ)
    (Phi : ℝ → Vec (a + 1) → ℝ)
    (hdata : ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      IsOpenBox (D ε) ∧ z₀ ∈ D ε ∧ 0 < c ε ∧ 0 < C ε ∧
      (∃ L : ℝ≥0, LipschitzOnWith L (g ε) (D ε)) ∧
      (∀ z ∈ D ε, c ε ≤ u z) ∧
      countLawClosed P (D ε) ∧
      (∀ n t, ∀ᵐ ω ∂P.law n, normalized P n t ω ∈ D ε →
        ‖increment P n t ω‖ ≤ β) ∧
      (∀ n t, ∀ᵐ ω ∂P.law n, normalized P n t ω ∈ D ε →
        ‖meanIncrement P n t ω - (u (normalized P n t ω))⁻¹ • g ε (normalized P n t ω)‖ ≤
          C ε / scale n) ∧
      0 < sε ε ∧ zbar ε 0 = z₀ ∧ ContinuousOn (zbar ε) (Set.Icc 0 (sε ε)) ∧
      (∀ s ∈ Set.Icc 0 (sε ε), zbar ε s ∈ D ε ∧
        HasDerivWithinAt (zbar ε) (g ε (zbar ε s)) (Set.Icc 0 (sε ε)) s) ∧
      (∀ s ∈ Set.Ico 0 (sε ε), ε < h (zbar ε s)) ∧ h (zbar ε (sε ε)) = ε ∧
      (∃ L : ℝ≥0, LipschitzWith L (Phi ε)) ∧
      (∀ t₁ : ℕ → ℕ, ∃ error failure : ℕ → ℝ,
        (∀ n, 0 ≤ error n ∧ 0 ≤ failure n) ∧
        Tendsto error atTop (𝓝 0) ∧ Tendsto failure atTop (𝓝 0) ∧
        ∀ᶠ n in atTop, ((P.law n) {ω |
          ‖normalized P n (t₁ n) ω - zbar ε (sε ε)‖ ≤ ε ∧
          K * ε * scale n + error n * scale n <
            |((run n (N n) ω).2.card : ℝ) - ((run n (t₁ n) ω).2.card : ℝ) -
              scale n * Phi ε (normalized P n (t₁ n) ω)|}).toReal ≤ failure n))
    (Λ : ℝ)
    (hlimit : Tendsto (fun ε => zbar ε (sε ε) (Fin.last a) + Phi ε (zbar ε (sε ε)))
      (𝓝[>] 0) (𝓝 Λ)) :
    tendsInProbability P (fun n ω => ((run n (N n) ω).2.card : ℝ) / scale n) Λ ∧
    Tendsto (fun n => ∫ ω, ((run n (N n) ω).2.card : ℝ) / scale n ∂P.law n)
      atTop (𝓝 Λ) := by sorry

end FluidGreedyMatching.CliqueBomb
