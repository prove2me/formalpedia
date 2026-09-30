-- Prove2me | Theorems.Thm_ComputationalLearning_product_estimate_error
-- name    : ComputationalLearning.product_estimate_error
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:23:35.521702+00:00
-- url     : https://prove2.me/theorems/5334058c-50d9-45fe-b32d-5f967ada4d94
-- title:
--   p. 115: for A, B, Â, B̂ ∈ [0,1] with |A − Â|, |B − B̂| ≤ τ', AB − 2τ' ≤ ÂB̂ ≤ AB + 3τ'
-- statement:
--   **p. 115.** For any $A, B \in [0, 1]$ and $\hat A, \hat B \in [0, 1]$ that satisfy $A - \tau' \le \hat A \le A + \tau'$ and $B - \tau' \le \hat B \le B + \tau'$ for some $\tau' \in [0, 1]$, we have $AB - 2\tau' \le \hat A\hat B \le AB + 3\tau'$. Thus if we are using the product of the estimates $\hat A$ and $\hat B$ to estimate the product $AB$ within additive error $\tau$, then $\tau' = \tau/3$ suffices.
--
--   Formally: the two inequalities, for reals $A, B, \hat A, \hat B, \tau' \in [0, 1]$ with $|A - \hat A| \le \tau'$ and $|B - \hat B| \le \tau'$.
-- source:
--   Kearns and Vazirani, An Introduction to Computational Learning Theory, MIT Press 1994, doi:10.7551/mitpress/3897.001.0001, §5.4.2 p. 115, the error propagation through a product of estimates

import Definitions.Def_ComputationalLearning_Noise

open MeasureTheory ProbabilityTheory

namespace ComputationalLearning

/-- **Error propagation through a product** (§5.4.2, p. 115): for any `A, B ∈ [0, 1]` and
estimates `Â, B̂ ∈ [0, 1]` with `|A − Â| ≤ τ'` and `|B − B̂| ≤ τ'` for some `τ' ∈ [0, 1]`,
`AB − 2τ' ≤ ÂB̂ ≤ AB + 3τ'`; thus `τ' = τ/3` suffices to estimate a product within `τ`. -/
theorem product_estimate_error {A B Ah Bh τ' : ℝ} (hA : A ∈ Set.Icc (0 : ℝ) 1)
    (hB : B ∈ Set.Icc (0 : ℝ) 1) (hAh : Ah ∈ Set.Icc (0 : ℝ) 1) (hBh : Bh ∈ Set.Icc (0 : ℝ) 1)
    (hτ : τ' ∈ Set.Icc (0 : ℝ) 1) (h1 : |A - Ah| ≤ τ') (h2 : |B - Bh| ≤ τ') :
    A * B - 2 * τ' ≤ Ah * Bh ∧ Ah * Bh ≤ A * B + 3 * τ' := by sorry

end ComputationalLearning
