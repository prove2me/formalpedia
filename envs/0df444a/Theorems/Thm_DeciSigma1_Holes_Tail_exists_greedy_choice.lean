-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_exists_greedy_choice
-- name    : DeciSigma1.Holes.Tail.exists_greedy_choice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:59:03.810254+00:00
-- url     : https://prove2.me/theorems/32a898a7-02ef-4d8e-9146-3bd45f1f9281
-- title:
--   Tail: exists greedy choice
-- statement:
--   Greedy choice of values for the coordinates of `P`, given the values `Ω₀` on a disjoint set
--   `U₀`. Suppose that for each `v ∈ P` and any admissible values (`Adm`) on a set `U` of other
--   coordinates, some good value (`Good`) for `v` is compatible (`Compat`) with all of them, that
--   good values are admissible, and that compatibility between good values is symmetric. Then some
--   values, equal to `Ω₀` on `U₀` and good on `P`, make the value of each `v ∈ P` compatible with
--   the value of every other coordinate of `U₀ ∪ P`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayFamilies.lean#L50-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayFamilies.lean#L50-L93

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Candidates
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_WindowChains
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayFamilies
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Tail.exists_greedy_choice {ι ρ : Type*} [DecidableEq ι] {U₀ P : Finset ι}
    (hdisj : Disjoint U₀ P) (Ω₀ : ι → ρ) (Adm Good : ι → ρ → Prop)
    (Compat : ι → ρ → ι → ρ → Prop) (hU₀ : ∀ u ∈ U₀, Adm u (Ω₀ u))
    (hAdm : ∀ v ∈ P, ∀ x, Good v x → Adm v x)
    (hsymm : ∀ v ∈ P, ∀ w ∈ P, ∀ x y, Good v x → Good w y → Compat v x w y → Compat w y v x)
    (hstep : ∀ v ∈ P, ∀ (U : Finset ι) (Ω : ι → ρ), v ∉ U → (∀ u ∈ U, Adm u (Ω u)) →
      ∃ x, Good v x ∧ ∀ u ∈ U, Compat v x u (Ω u)) :
    ∃ Ω : ι → ρ, (∀ u ∈ U₀, Ω u = Ω₀ u) ∧ (∀ v ∈ P, Good v (Ω v)) ∧
      ∀ v ∈ P, ∀ u ∈ U₀ ∪ P, u ≠ v → Compat v (Ω v) u (Ω u) := by sorry
