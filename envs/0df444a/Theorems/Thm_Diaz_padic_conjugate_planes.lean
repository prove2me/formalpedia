-- Prove2me | Theorems.Thm_Diaz_padic_conjugate_planes
-- name    : Diaz.padic_conjugate_planes
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T09:10:52.463209+00:00
-- url     : https://prove2.me/theorems/62f03b8a-69b8-478b-a269-8253f176212c
-- title:
--   The multiplier set of a point of one conjugate plane is exactly the opposite plane
-- statement:
--   **Source.** Carlo Perassi's p-adic multiplier bound for conjugate planes — its second half, the identification of the multiplier
--   set.
--
--   **Statement, as formalised.** Let `F` be a field, `A ⊆ F` a subfield, and `V ⊆ F` a set
--   containing `1`, closed under addition and under multiplication by `A`. Let `u, v ∈ V` with
--   `u v ∈ A` and `v ∉ A`, and let `x = a + b u` with `a, b ∈ A`. Assume the multiplier bound
--
--   > any three elements of `M_x = {y ∈ V : x y ∈ V}` are `A`-linearly dependent.
--
--   Then `M_x = A ⊕ A v`.
--
--   **Why this is the p-adic statement.** There `F = ℂ_p`, `A = ℚ̄`,
--   `V = Λ_p = ℚ̄ + span_ℚ̄ ℒ_p` with `ℒ_p = {log_p α : α ∈ ℚ̄^×}` the Iwasawa logarithms of
--   algebraic numbers, `u ∈ 𝒟_p` a point of the p-adic Diaz locus and `v = σ u` its image under
--   the Galois involution of the fixed quadratic extension `K/ℚ_p`; `u v = N(u) ∈ ℚ̄` is the
--   norm, the ultrametric replacement for the archimedean modulus. `U_+ = ℚ̄ ⊕ ℚ̄ u` and
--   `U_- = ℚ̄ ⊕ ℚ̄ σu` are the two conjugate planes, and the claim is `M_x = U_-` for every
--   `x ∈ U_+ ∖ ℚ̄`.
--
--   The involution itself never enters the argument: only that `v` is a second element of `V`
--   with `u v ∈ A`. So `σ` is dropped from the statement and `v` left free. Similarly `Λ_p`
--   appears only through the three closure properties actually used, and `ℂ_p` — which cannot be
--   built here without a permanent definition node — only as an arbitrary field. Nothing is lost:
--   the intended instance satisfies every hypothesis.
--
--   **What is a hypothesis and why.** Two inputs are cited rather than proved.
--
--   * The **multiplier bound** `dim_A M_x ≤ 2`, which in the p-adic setting comes from the p-adic
--     strong six exponentials theorem of Waldschmidt and Roy (Corollary 2.2.2 of Maksoud). Its
--     elementary half is the separate node `Diaz.rank_one_six_exponentials`; the transcendence
--     half is unavailable, so the bound is the hypothesis `hbound`, stated concretely as
--     "any three elements of `M_x` are `A`-dependent".
--   * `v ∉ A`, which in the p-adic setting is **Mahler's p-adic Hermite–Lindemann theorem**
--     `ℒ_p ∩ ℚ̄ = {0}`, and is what makes `dim_A U_- = 2` rather than `1`.
--
--   What is proved is the assembly: the inclusion `U_- ⊆ M_x` is the identity
--   `(a + bu)(C + Dv) = (aC + bD·uv) + (bC)u + (aD)v`, which the closure properties keep inside
--   `V`; the reverse inclusion applies the bound to the triple `1, v, y` and uses `v ∉ A` to
--   force the coefficient of `y` to be non-zero. Over `ℂ` with `v = conj u` the same identity is
--   already on this mission as `Diaz.conj_planes_mul`, and the independence of `1, u` as
--   `Diaz.conj_planes_inter`; this node is the ultrametric form of both, with the multiplier
--   bound added so that the inclusion becomes an equality.
--
--   **Not in the companion note.** This statement is not in Carlo Perassi's companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9), which does not treat the p-adic setting; it is unpublished apart from this node. It was left out for scope, not withdrawn as wrong.
--
--   **Novelty.** No novelty is claimed, either for the mathematics or for the formalisation.
--   Carlo Perassi presents this material as the transfer of a complex argument to
--   another setting.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.padic_conjugate_planes {F : Type*} [Field F] (A : Subfield F) (V : Set F)
    (hVadd : ∀ y ∈ V, ∀ z ∈ V, y + z ∈ V)
    (hVmul : ∀ c ∈ A, ∀ y ∈ V, c * y ∈ V)
    (hone : (1 : F) ∈ V)
    {u v : F} (hu : u ∈ V) (hv : v ∈ V) (hq : u * v ∈ A) (hvA : v ∉ A)
    {x a b : F} (ha : a ∈ A) (hb : b ∈ A) (hx : x = a + b * u)
    (hbound : ∀ y₁ y₂ y₃ : F, y₁ ∈ V → x * y₁ ∈ V → y₂ ∈ V → x * y₂ ∈ V →
      y₃ ∈ V → x * y₃ ∈ V →
      ∃ c₁ ∈ A, ∃ c₂ ∈ A, ∃ c₃ ∈ A,
        ¬ (c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0) ∧ c₁ * y₁ + c₂ * y₂ + c₃ * y₃ = 0) :
    ∀ y : F, (y ∈ V ∧ x * y ∈ V) ↔ ∃ C ∈ A, ∃ D ∈ A, y = C + D * v := by sorry
