-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_Herm4_iso_of
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.Herm4.iso_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:13:55.998674+00:00
-- url     : https://prove2.me/theorems/f1385b45-b5a8-4de7-9e57-5870d68c7cce
-- title:
--   Herm4: iso of
-- statement:
--   The Herm4 construction uses the iso of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PFourSq.lean#L150-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PFourSq.lean#L150-L205

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
variable {K : Type} [Field K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (c : K →+* K) (h : V → V → K)
variable {c h}

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.Herm4.iso_of (H : Herm4 c h) {n : Type} [Fintype n] [DecidableEq n] (b : Basis n K V)
    (hb : ∀ i j, i ≠ j → h (b i) (b j) = 0) (p q r s : n → K) (hp : ∀ i, c (p i) = p i) (hq : ∀ i, c (q i) = q i)
    (hr : ∀ i, c (r i) = r i) (hs : ∀ i, c (s i) = s i)
    (hsq : ∀ i, h (b i) (b i) = p i ^ 2 + q i ^ 2 + r i ^ 2 + s i ^ 2) :
    ∃ g : (Fin 4 → V) ≃ₗ[K] (Fin 4 × n → K), (∀ x y, ∑ w, g x w * c (g y w) = ∑ a, h (x a) (y a)) ∧
      ∀ x w, g x w = ∑ a, qM (p w.2) (q w.2) (r w.2) (s w.2) w.1 a * b.repr (x a) w.2 := by sorry
