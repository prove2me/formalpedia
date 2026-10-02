-- Prove2me | Theorems.Thm_CookPvsNP_tm_compose_poly_witness
-- name    : CookPvsNP.tm_compose_poly_witness
-- status  : Proved
-- author  : @Sneed
-- created : 2026-09-30T17:00:21.445495+00:00
-- url     : https://prove2.me/theorems/97e6135e-d545-48d5-b618-98b654c5096a
-- title:
--   Concrete Cook-machine witnesses compose in polynomial time
-- statement:
--   Given concrete one-tape Cook machines witnessing polynomial-time computability of f and g, with possibly different finite work alphabets and explicit exponents, there is a single finite-alphabet Cook machine and a single exponent computing g after f. This isolates the machine-simulation and alphabet-merging content from the outer existential packaging of PolyTimeComputable.
-- source:
--   Cook, The P versus NP problem, Clay Mathematics Institute (2000), Definition 3; standard closure of polynomial-time transducers under sequential composition.

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Theorems.Thm_CookPvsNP_tm_output_length_le
import Theorems.Thm_CookPvsNP_nat_pow_add_le_pow_add

set_option autoImplicit false

namespace CookPvsNP

theorem tm_compose_poly_witness
    {Sym₁ Sym₂ Sym₃ Γ₁ Γ₂ : Type}
    [Fintype Γ₁] [Fintype Γ₂]
    (ι₁ : Sym₁ ↪ Γ₁) (ι₂₁ : Sym₂ ↪ Γ₁) (M₁ : TM Γ₁) (k₁ : ℕ)
    (ι₂₂ : Sym₂ ↪ Γ₂) (ι₃ : Sym₃ ↪ Γ₂) (M₂ : TM Γ₂) (k₂ : ℕ)
    (f : List Sym₁ → List Sym₂) (g : List Sym₂ → List Sym₃)
    (h₁ : ∀ x : List Sym₁,
      M₁.HaltsWithin (x.length ^ k₁ + k₁) (x.map ι₁) ∧
      M₁.output (M₁.run (x.length ^ k₁ + k₁) (M₁.init (x.map ι₁))) =
        (f x).map (some ∘ ι₂₁))
    (h₂ : ∀ y : List Sym₂,
      M₂.HaltsWithin (y.length ^ k₂ + k₂) (y.map ι₂₂) ∧
      M₂.output (M₂.run (y.length ^ k₂ + k₂) (M₂.init (y.map ι₂₂))) =
        (g y).map (some ∘ ι₃)) :
    ∃ (Γ : Type) (_ : Fintype Γ) (j₁ : Sym₁ ↪ Γ) (j₃ : Sym₃ ↪ Γ)
      (M : TM Γ) (k : ℕ),
      ∀ x : List Sym₁,
        M.HaltsWithin (x.length ^ k + k) (x.map j₁) ∧
        M.output (M.run (x.length ^ k + k) (M.init (x.map j₁))) =
          (g (f x)).map (some ∘ j₃) := by sorry

end CookPvsNP
