-- Prove2me | solution 1 for sgDiv_wreath_decoration_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:02:09.561363+00:00
-- url     : https://prove2.me/submissions/1b955666-4a3b-411e-b405-a03c63faaadd

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_LocalDivisor
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_Foundations_Division
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_Cayley
public import Definitions.Def_KrohnRhodes_Foundations_ConstantMaps
public import Definitions.Def_KrohnRhodes_FactorTower

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.style.show false
set_option linter.unusedSectionVars false
universe u
open Green
theorem _root_.solution (A A' B X : Type u) [Monoid A] [Finite A]
    [Monoid A'] [Finite A'] [Monoid B] [Finite B] [Fintype X] [MulAction B X]
    (h : SgDiv A A') :
    SgDiv (WreathProduct A B X) (WreathProduct A' B X) := by
  obtain ⟨U', φ', hφ'⟩ := h
  let U : Subsemigroup (WreathProduct A' B X) :=
    { carrier := {w | ∀ x, w.func x ∈ U'}
      mul_mem' := by
        rintro a b ha hb x
        rw [WreathProduct.mul_func]
        exact U'.mul_mem (ha _) (hb _) }
  refine ⟨U, ⟨fun w => ⟨fun x => φ' ⟨w.1.func x, w.2 x⟩, w.1.base⟩, ?_⟩, ?_⟩
  · rintro ⟨p, hp⟩ ⟨q, hq⟩
    apply WreathProduct.ext
    · funext x
      show φ' ⟨(p * q).func x, _⟩ = φ' ⟨p.func (q.base • x), _⟩ * φ' ⟨q.func x, _⟩
      rw [← φ'.map_mul]; congr 1
    · rfl
  · intro w
    choose g hg using fun x => hφ' (w.func x)
    refine ⟨⟨⟨fun x => (g x : A'), w.base⟩, fun x => (g x).2⟩, ?_⟩
    apply WreathProduct.ext
    · funext x
      show φ' ⟨(g x : A'), _⟩ = w.func x
      have : φ' (g x) = w.func x := hg x
      rw [← this]
    · rfl
