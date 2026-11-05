-- Prove2me | solution 1 for finiteHereditaryMaximalSupergraph__p2m_3647f07c_750e_4c3e_8be8_ca29b1e4d823_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T17:16:28.287927+00:00
-- url     : https://prove2.me/submissions/640a56a5-5963-411d-801c-ab1033f0b738

import Mathlib

set_option linter.unusedVariables false

theorem solution
    {V : Type} [Fintype V] [DecidableEq V] (P : SimpleGraph V → Prop)
    (hmono : ∀ ⦃G J : SimpleGraph V⦄, G ≤ J → P J → P G)
    (K : SimpleGraph V) (hK : P K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ P H ∧
      (∀ J : SimpleGraph V, H ≤ J → P J → J ≤ H) := by
  classical
  let p : SimpleGraph V → Prop := fun H => P H ∧ K ≤ H
  have hpK : p K := ⟨hK, le_rfl⟩
  obtain ⟨H, hKH, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := K) hpK)
  rcases hmax with ⟨hpH, hmax'⟩
  refine ⟨H, hpH.2, hpH.1, ?_⟩
  intro J hHJ hPJ
  exact hmax' ⟨hPJ, hpH.2.trans hHJ⟩ hHJ
