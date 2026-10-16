-- Prove2me | Theorems.Thm_BreakingSample_PolicyEval_eq_82
-- name    : BreakingSample.PolicyEval.eq_82
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:02:47.294917+00:00
-- url     : https://prove2.me/theorems/5c50f0f0-652c-4635-a87f-d1666ef1a6b4
-- title:
--   (82), p. 27 — for a fixed π, w.p. ≥ 1 − δ, |(P̂_π − P_π)V⁽ˡ⁾| ≤ √(2log(4m|S|/δ)/N)√Var_{P_π}[V⁽ˡ⁾] + ‖V⁽ˡ⁾‖∞log(4m|S|/δ)/N for all 0 ≤ l ≤ m
-- statement:
--   Let $(P,r,\gamma)$ be a discounted MDP in the standing setting (finite states and actions, $P$ a transition kernel, $r\in[0,1]$, $0<\gamma<1$), $\pi$ a deterministic policy fixed in advance, $0<\delta<1$ and $N\ge1$. Draw $N$ independent samples from the generative model at every state-action pair and let $\widehat P$ be the empirical kernel (3). Let $V^{(l)}$ be the auxiliary vectors (36), built from the **true** kernel $P$, put $m=\log\frac{e}{1-\gamma}$ and
--   $$
--   L=\log\Big(\frac{4m|\mathcal S|}{\delta}\Big).
--   $$
--   Then with probability at least $1-\delta$,
--   $$
--   \big|(\widehat P_\pi-P_\pi)V^{(l)}\big|\le\sqrt{\frac{2L}{N}}\sqrt{\mathrm{Var}_{P_\pi}\big[V^{(l)}\big]}+\frac{\|V^{(l)}\|_\infty L}{N}\mathbf 1
--   $$
--   holds entrywise, simultaneously for all integers $0\le l\le m$.
--
--   Thus the Bernstein-type condition of Lemma 2 holds with $\beta_1=2L$ for a data-independent policy; this is the only probabilistic ingredient of Lemma 1.
--
--   **Formalization Note** The probability is the finite sum over data sets of their product weights; the claim is written as "the probability that the bound fails for some $l$ and some state is at most $\delta$". $N>0$ is the standing assumption of (3).
-- source:
--   arXiv:2005.12900v8, (82), App. B.1, proof of Lemma 1, p. 27

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Model
import Definitions.Def_BreakingSample_Perturbed_Sampling

namespace BreakingSample.PolicyEval

open Matrix

/-- (82), arXiv:2005.12900v8, App. B.1, proof of Lemma 1, p. 27: for a fixed policy `π`, with
probability at least `1 − δ` over the data, the Bernstein-type bound
`|(P̂_π − P_π)V⁽ˡ⁾| ≤ √(2 log(4m|S|/δ)/N) √Var_{P_π}[V⁽ˡ⁾] + ‖V⁽ˡ⁾‖∞ log(4m|S|/δ)/N`
holds for all integers `0 ≤ l ≤ m`, where `m = log(e/(1−γ))` and the `V⁽ˡ⁾` of (36) are built from
the true kernel `P`. -/
theorem eq_82 {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : BreakingSample.Perturbed.IsDiscountedMDP P r γ)
    (π : S → A) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (N : ℕ) (hN : 0 < N) :
    let m : ℝ := Real.log (Real.exp 1 / (1 - γ))
    let L : ℝ := Real.log (4 * m * (Fintype.card S : ℝ) / δ)
    BreakingSample.Perturbed.sampleProb P N (fun x => ¬ ∀ l : ℕ, (l : ℝ) ≤ m → ∀ s,
      |((BreakingSample.Perturbed.policyMatrix (BreakingSample.Perturbed.empKernel x) π - BreakingSample.Perturbed.policyMatrix P π) *ᵥ BreakingSample.Perturbed.auxV P r γ π l) s|
        ≤ Real.sqrt (2 * L / N) * Real.sqrt (BreakingSample.Perturbed.varPi P π (BreakingSample.Perturbed.auxV P r γ π l) s)
          + ‖BreakingSample.Perturbed.auxV P r γ π l‖ * L / N) ≤ δ := by sorry

end BreakingSample.PolicyEval
