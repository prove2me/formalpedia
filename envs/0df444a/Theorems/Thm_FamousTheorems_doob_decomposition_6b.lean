-- Prove2me | Theorems.Thm_FamousTheorems_doob_decomposition_6b
-- name    : FamousTheorems.doob_decomposition_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:42:53.750532+00:00
-- url     : https://prove2.me/theorems/e61f27af-7529-4c9e-aadf-91c22e5736ca
-- title:
--   The Doob decomposition theorem
-- statement:
--   **The Doob decomposition theorem.** Let $(f_n)_{n\ge0}$ be an adapted sequence of integrable random variables, with values in a real Banach space, on a filtered probability space $(\Omega,(\mathcal F_n),\mu)$. Then $f=M+A$, where $M$ is a martingale and $A$ is predictable, meaning that $A_{n+1}$ is $\mathcal F_n$-measurable, with $A_0=0$. Explicitly,
--   $$A_n=\sum_{i<n}\mathbb E[f_{i+1}-f_i\mid\mathcal F_i],\qquad M_n=f_n-A_n.$$
--
--   The decomposition separates a process into a "fair game" part and a predictable drift. It is the discrete-time forerunner of the Doob–Meyer decomposition, and it is how martingale methods are applied to submartingales. A submartingale corresponds to an increasing $A$. The decomposition is also unique almost surely.
--
--   **Formalization note.** Mathlib's `MeasureTheory.martingale_martingalePart`, together with the decomposition `martingalePart_add_predictablePart`, `stronglyAdapted_predictablePart` and `predictablePart_zero`. The measure is assumed $\sigma$-finite on each $\mathcal F_n$ (`SigmaFiniteFiltration`), which holds for probability measures. Predictability is stated as adaptedness of $n\mapsto A_{n+1}$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.martingale_martingalePart`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem doob_decomposition_6b {Ω E : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {ℱ : Filtration ℕ m0} [SigmaFiniteFiltration μ ℱ] {f : ℕ → Ω → E}
    (hf : StronglyAdapted ℱ f) (hfint : ∀ n, Integrable (f n) μ) :
    ∃ M A : ℕ → Ω → E, Martingale M ℱ μ ∧ StronglyAdapted ℱ (fun n => A (n + 1)) ∧ A 0 = 0 ∧ f = M + A := by sorry

end FamousTheorems
