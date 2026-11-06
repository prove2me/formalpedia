-- Prove2me | Theorems.Thm_BlockBochner_fact_10
-- name    : BlockBochner.fact_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:36:02.613473+00:00
-- url     : https://prove2.me/theorems/88241f20-3378-499f-b631-702abcfcd391
-- title:
--   Fact 10 — spectral gap from Laplacian bounds
-- statement:
--   Let $L$ be a bounded, self-adjoint, nonnegative operator on a real Hilbert space $H$, and let $\Pi$ be the orthogonal projection onto $(\ker L)^\perp$. For $\gamma>0$ the following are equivalent:
--   1. $\sigma(L)\subseteq\{0\}\cup[\gamma,\infty)$;
--   2. $\gamma\|\Pi f\|^2\le\langle f,Lf\rangle$ for every $f\in H$;
--   3. $\gamma\langle f,Lf\rangle\le\|Lf\|^2$ for every $f\in H$.
--
--   In the proof of Theorem 3 it turns the Poincaré inequality for the block dynamics into the spectral-gap conclusion.
--
--   Differences from the source: none.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Fact 10, p.14

import Mathlib

namespace BlockBochner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Fact 10.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Fact 10, p.14. Let `L` be a bounded, self-adjoint, nonnegative operator on `H`
and `Π` the orthogonal projection onto `(ker L)^⊥`. For `γ > 0` the following are equivalent:
`σ(L) ⊆ {0} ∪ [γ, ∞)`; `γ‖Πf‖² ≤ ⟨f, Lf⟩` for all `f`; `γ⟨f, Lf⟩ ≤ ‖Lf‖²` for all `f`.

**Formalization Note** `σ(L)` is the real spectrum of `L` in the algebra of bounded operators. -/
theorem fact_10 (L : H →L[ℝ] H) (hsa : IsSelfAdjoint L) (hpos : ∀ f, 0 ≤ inner ℝ f (L f))
    {γ : ℝ} (hγ : 0 < γ) :
    List.TFAE [spectrum ℝ L ⊆ {0} ∪ Set.Ici γ,
      ∀ f, γ * ‖(LinearMap.ker L.toLinearMap)ᗮ.starProjection f‖ ^ 2 ≤ inner ℝ f (L f),
      ∀ f, γ * inner ℝ f (L f) ≤ ‖L f‖ ^ 2] := by sorry

end BlockBochner
