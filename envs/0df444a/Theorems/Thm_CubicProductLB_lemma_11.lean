-- Prove2me | Theorems.Thm_CubicProductLB_lemma_11
-- name    : CubicProductLB.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:18:07.985857+00:00
-- url     : https://prove2.me/theorems/93222123-8920-4304-8d44-b6be226fb223
-- title:
--   Lemma 11 — quadratic-unit dichotomy
-- statement:
--   Let $P$ have a quadratic representation on $X_n$ and satisfy $P(x) \ne 0$ on $X_n$. Then at least one of the following holds:
--
--   1. $P(x) = \varepsilon(1 + L(x)^2)$ for every $x \in X_n$, for an affine form $L$ and $\varepsilon \in \{1, -1\}$;
--   2. $P$ is an eight-junta.
--
--   The statement also applies to a signed raw factor each of whose monomials has odd exponent on at most two coordinates. A nowhere-zero quadratic is therefore either one affine test up to sign or a function of boundedly many coordinates.
--
--   **Formalization Note** Both sentences of the lemma are stated, as a conjunction; a raw factor is a listed factor.
--
--   Differences from the source:
--   - encoding: P a polynomial with a quadratic representation → any function f with multilinear degree at most 2 on X_n; reason: the condition and the conclusions concern only the values on X_n; same instances
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Lemma 11, p.15

import Mathlib
import Definitions.Def_CubicProductLB_signCube
import Definitions.Def_CubicProductLB_ListedFactor
import Definitions.Def_CubicProductLB_HasMultilinearDegLE
import Definitions.Def_CubicProductLB_AffineForm
import Definitions.Def_CubicProductLB_IsJunta

namespace CubicProductLB

/-- Lemma 11 (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Lemma 11, p.15). A nowhere-zero function on `X_n` with a quadratic representation
is `ε(1 + L²)` on `X_n` for an affine form `L` and `ε ∈ {1, -1}`, or is an eight-junta. The same holds
for a signed raw factor each of whose monomials has odd exponent on at most two coordinates.

**Formalization Note** "Quadratic representation" is `HasMultilinearDegLE 2`. "At least one of" is an
inclusive disjunction. Both sentences of the lemma are stated. -/
theorem lemma_11 {n : ℕ} :
    (∀ f : (Fin n → ZMod 3) → ZMod 3, HasMultilinearDegLE 2 f → (∀ x ∈ signCube n, f x ≠ 0) →
      (∃ (L : AffineForm n) (e : ZMod 3), (e = 1 ∨ e = -1) ∧
        ∀ x ∈ signCube n, f x = e * (1 + AffineForm.eval L x ^ 2)) ∨ IsJunta 8 f) ∧
    (∀ l : ListedFactor n,
      (∀ m ∈ l, (Finset.univ.filter fun i => Odd (m.exps i)).card ≤ 2) →
      (∀ x ∈ signCube n, ListedFactor.eval l x ≠ 0) →
      (∃ (L : AffineForm n) (e : ZMod 3), (e = 1 ∨ e = -1) ∧
        ∀ x ∈ signCube n, ListedFactor.eval l x = e * (1 + AffineForm.eval L x ^ 2)) ∨
        IsJunta 8 (ListedFactor.eval l)) := by sorry

end CubicProductLB
