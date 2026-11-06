-- Prove2me | Theorems.Thm_FasterSFM_lemma_16
-- name    : FasterSFM.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:34:30.475338+00:00
-- url     : https://prove2.me/theorems/ee2d1f0a-a7af-42f0-9e5b-5fb8fa392bd3
-- title:
--   Lemma 16 — accuracy of the converted certificate and the full-certificate guard
-- statement:
--   Let $h$ be submodular, the current DAG $D$ (with $N$ blocks of the ground set of size $n$) calibrated at $t$ with $h(\emptyset),h(U)\ge h(\emptyset)+1-t$. Let $a_i$ be stored nonzero current compressed rows on the blocks, each summing to $0$; each greedy row satisfies Lemma 4's bound $a_i(X)\le H_t(X)-(t-t_i)$ on proper nonempty closed sets with timestamp $t_i\le t$, and each graph row satisfies $a_i(X)\le0$ on closed sets. Put $\tilde a_{i,C}=a_{i,C}/\sqrt{|C|}$, $\sigma_i=\|\tilde a_i\|_2$, $b_i=\tilde a_i/\sigma_i$. Let $p$ be simplex weights with
--
--   $$\Big\|\sum_ip_ib_i\Big\|_2\le2\chi_n, \tag{17}$$
--
--   and convert them by $Z=\sum_ip_i/\sigma_i$, $\alpha_i=(p_i/\sigma_i)/Z$. If the support size $r$ is at most $k_n$, then
--
--   $$\frac{\|y\|_1}{L}\ \le\ \sqrt n\,\Big\|\sum_ip_ib_i\Big\|_2\ \le\ e_n:=2\sqrt n\,Q_n\delta, \tag{18}$$
--
--   the greedy weight $\theta$ is positive, $\Delta\ge\beta$ certifies $H_t(X)\ge0$ on every proper nonempty closed set and, under invariant (1) at $t$ (every $Y$ with $h_s(Y)\le0$ for some $s\ge t$ is the lift of a closed set), the optimality of the witness: $h(\emptyset)+1-t\le h(Y)$ for every $Y\subseteq U$, and either $\Delta\ge\beta$ or (7) $L>4N^2G+4N\beta$ holds.
--
--   The lemma connects the geometric certificate of §6 to the combinatorial arc extraction of §4.3.
--
--   Differences from the source:
--   - reading: the algorithm's context (calibrated DAG, historical vectors, support r ≤ k_n by Lemma 13) → explicit hypotheses: EndpointsAbove h t, calibration, Lemma 4's bounds with t_i ≤ t, graph bounds, r ≤ k_n; reason: reading R7
--   - generalization: the simplex weights p supplied by Lemma 15 → any simplex weights p satisfying (17); reason: (17) is the only property used
--   - generalization: the quotient DAG of the implication graph (SCCs contracted) → any partition of Fin n into N nonempty blocks with an acyclic arc relation on the blocks; reason: the lemma's proof uses only these properties (reading R8); the quotient DAG is one instance
--   - reading: "∆ ≥ β, which certifies optimality of the witness set" → ∆ ≥ β implies H_t(X) ≥ 0 on every proper nonempty closed X, and, under invariant (1) at t, h(∅) + 1 − t ≤ h(Y) for every Y ⊆ U; reason: reading R7: the witness attains m = h(∅) + 1 − t (p.9), so the second conclusion is its optimality; invariant (1) is the algorithm's fact made explicit
-- source:
--   Ene & Nguyen, A Faster Strongly Polynomial Time Algorithm for Submodular Function Minimization, arXiv:2610.25403v1, Lemma 16, eqs. (17)–(18), p.28

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_FasterSFM_Params
import Definitions.Def_FasterSFM_BlockDAG

namespace FasterSFM

open Classical

/-- **Lemma 16** (Accuracy and the full-certificate guard), p.28.

Ene & Nguyen, arXiv:2610.25403v1, Lemma 16, eqs. (17)–(18), p.28.

"For a certificate drawn from the inserted rows, the converted certificate has
‖y‖₁ / L ≤ √n ‖Σ_i p_i b_i‖₂ ≤ e_n := 2√n Q_n δ. (18)
The sum θ of the greedy coefficients is positive. Either ∆ ≥ β, which certifies optimality of the
witness set, or the condition (7) holds, enabling arc extraction."

Setting (p.28): stored nonzero current compressed rows `a_i` on the `N` blocks, each summing to `0`,
with `ã_{i,C} = a_{i,C}/√|C|`, `σ_i = ‖ã_i‖₂`, `b_i = ã_i/σ_i`; simplex weights `p` with (17)
`‖Σ_i p_i b_i‖₂ ≤ 2χ_n`; `Z = Σ_i p_i/σ_i` and `α_i = (p_i/σ_i)/Z`; `y, L, β, θ, ∆, r, G` as in §4.3.

**Formalization Note.**
* Reading R7: the facts the algorithm supplies are hypotheses: `EndpointsAbove h t`; calibration;
  each greedy term satisfies Lemma 4's bound `a_i(X) ≤ H_t(X) − (t − t_i)` on proper nonempty closed
  sets with `t_i ≤ t`; each graph term satisfies `a_i(X) ≤ 0` on closed sets; the support has size
  `r ≤ k_n` (Lemma 13). `N ≤ n` holds because every block is nonempty.
* "∆ ≥ β certifies optimality of the witness set" is stated as: `∆ ≥ β` implies `H_t(X) ≥ 0` on every
  proper nonempty closed set (the paper's certificate, p.13), and, under invariant (1) at `t` (every
  `Y` with `h_s(Y) ≤ 0` for some `s ≥ t` is the lift of a closed set, p.9), the witness value
  `m = h(∅) + 1 − t` is at most `h(Y)` for every `Y ⊆ U`: the witness is a minimizer. -/
theorem lemma_16 {n N m : ℕ} (h : Finset (Fin n) → ℝ) (hsub : NonmonotoneSubmod.Shared.Submodular h)
    (D : BlockDAG n N) (t : ℝ) (hend : EndpointsAbove h t) (hcal : D.Calibrated h t)
    (a : Fin m → Fin N → ℝ) (grd : Fin m → Bool) (stamp : Fin m → ℝ) (p : Fin m → ℝ)
    (ha0 : ∀ i, a i ≠ 0) (hsum : ∀ i, ∑ v, a i v = 0)
    (hgreedy : ∀ i, grd i = true → ∀ X, D.Closed X → X.Nonempty → X ≠ Finset.univ →
      setSum (a i) X ≤ D.Hs h t X - (t - stamp i))
    (hstamp : ∀ i, grd i = true → stamp i ≤ t)
    (hgraph : ∀ i, grd i = false → ∀ X, D.Closed X → setSum (a i) X ≤ 0)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    let atl : Fin m → Fin N → ℝ := fun i C => a i C / Real.sqrt (D.blockSize C)
    let σ : Fin m → ℝ := fun i => Real.sqrt (∑ C, atl i C ^ 2)
    let b : Fin m → Fin N → ℝ := fun i C => atl i C / σ i
    let pb : ℝ := Real.sqrt (∑ C, (∑ i, p i * b i C) ^ 2)
    let Z : ℝ := ∑ i, p i / σ i
    let α : Fin m → ℝ := fun i => p i / σ i / Z
    pb ≤ 2 * chi n →
    (certSupp α : ℝ) ≤ kn n →
    (∑ v, |certY a α v|) / certL a α ≤ Real.sqrt n * pb ∧
    Real.sqrt n * pb ≤ en n ∧
    0 < certTheta α grd ∧
    (certBeta a α ≤ certDelta α grd stamp t →
      (∀ X, D.Closed X → X.Nonempty → X ≠ Finset.univ → 0 ≤ D.Hs h t X) ∧
      ((∀ s : ℝ, t ≤ s → ∀ Y : Finset (Fin n), h Y - h ∅ - 1 + s ≤ 0 →
          ∃ X, D.Closed X ∧ Y = D.lift X) →
        ∀ Y : Finset (Fin n), h ∅ + 1 - t ≤ h Y)) ∧
    (certBeta a α ≤ certDelta α grd stamp t ∨
      4 * (N : ℝ) ^ 2 * guardG n (certSupp α) (certBeta a α) (certDelta α grd stamp t) +
        4 * (N : ℝ) * certBeta a α < certL a α) := by sorry

end FasterSFM
