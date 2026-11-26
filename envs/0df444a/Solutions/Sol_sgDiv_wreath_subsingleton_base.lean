-- Prove2me | solution 1 for sgDiv_wreath_subsingleton_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:01:55.814706+00:00
-- url     : https://prove2.me/submissions/e59e3fb9-75fe-4324-b1d7-cc229e12672b

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
theorem _root_.solution (A B : Type u) [Monoid A] [Monoid B]
    [Subsingleton B] :
    SgDiv A (WreathProduct A B B) := by
  -- Embed `A` as `a ↦ ⟨fun _ => a, 1⟩`, with the top subsemigroup mapped back by
  -- evaluating the decoration at the (unique) point `1`.
  refine ⟨⊤, ⟨fun w => w.1.func 1, ?_⟩, ?_⟩
  · -- multiplicativity of the readout on the whole wreath:
    -- `(p * q).func 1 = p.func (q.base • 1) * q.func 1`, and `q.base • 1 = 1`
    -- since the base type is a subsingleton.
    rintro ⟨p, -⟩ ⟨q, -⟩
    show (p * q).func 1 = p.func 1 * q.func 1
    have hb : q.base • (1 : B) = (1 : B) := Subsingleton.elim _ _
    rw [WreathProduct.mul_func, hb]
  · -- surjectivity: hit `a` by `⟨fun _ => a, 1⟩`.
    intro a
    exact ⟨⟨⟨fun _ => a, 1⟩, Subsemigroup.mem_top _⟩, rfl⟩
