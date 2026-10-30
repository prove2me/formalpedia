-- Prove2me | Theorems.Thm_BundleShaping_NoOrderSet_lemma_2_c
-- name    : BundleShaping.NoOrderSet.lemma_2_c
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:12:10.217771+00:00
-- url     : https://prove2.me/theorems/63380641-76c6-4426-9753-8c11aecd6a91
-- title:
--   Lemma 2(c), p. 22 — in the modified problem one may take y_i = [Az]_i for i ∈ I⁻, so it reduces to (14)
-- statement:
--   In the bundle-to-stock model under the standing assumptions, fix a period $1\le t\le T$, a set $I^+$ of items (the no-order set, with complement $I^-$) and a net inventory $x\in\mathbb R^I$.
--
--   1. If $(y,z,q)$ is feasible for the modified problem, i.e. $y_{I^+}=x_{I^+}$, $y\ge Az$ and $q\in\Omega$, then the vector $y'$ with $y'_{I^+}=x_{I^+}$ and $y'_{I^-}=[Az]_{I^-}$ satisfies
--   $$y'_{I^+}=x_{I^+},\quad y'_{I^-}=[Az]_{I^-},\quad y'\ge Az,\quad q\in\Omega,\qquad G_t(y,z,q)\le G_t(y',z,q),$$
--   so $(y',z,q)$ is feasible for (14) and no worse.
--   2. Consequently every maximizer of (14) for $I^+$ is a maximizer of the modified problem for $I^+$.
--
--   This is the paper's statement $y^*_{it}(x_{I^+})=[Az^*_t(x_{I^+})]_i$ for $i\in I^-$ (in particular $y^*_t(\emptyset)=Az^*_t(\emptyset)$): the optimal order-up-to levels of the items that are ordered match the assembly plan exactly.
--
--   **Formalization Note.** The paper speaks of *the* maximizer; maximizers need not be unique, so the lemma is stated as the replacement property above together with the inclusion of the maximizers of (14) among those of the modified problem. The set (14) includes the constraint $y\ge Az$ (on $I^-$ it holds with equality; on $I^+$ it is $[Az]_{I^+}\le x_{I^+}$), which the printed (14) omits. Stated for $1\le t\le T$, where $G_t$ is defined.
-- source:
--   Song & Xue, Demand Shaping Through Bundling and Product Configuration, SSRN 3168907 (version of Aug. 19, 2020), p. 22, Lemma 2(c), modified problem and eq. (14)

import Mathlib
import Definitions.Def_BundleShaping_NoOrderSet_Model

namespace BundleShaping.NoOrderSet

open Matrix

variable {I J : Type} [Fintype I] [Fintype J]

theorem lemma_2_c [DecidableEq I] (P : Params I J) (hS : P.Standing) (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) (S : Finset I) (x : I → ℝ) :
    (∀ (y : I → ℝ) (z q : J → ℝ), P.FeasMod S x y z q →
      P.Feas14 S x (fun i => if i ∈ S then x i else (P.A *ᵥ z) i) z q ∧
      P.G t y z q ≤ P.G t (fun i => if i ∈ S then x i else (P.A *ᵥ z) i) z q) ∧
    (∀ (y : I → ℝ) (z q : J → ℝ), P.Max14 t S x y z q → P.MaxMod t S x y z q) := by sorry

end BundleShaping.NoOrderSet
