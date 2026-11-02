-- Prove2me | solution 1 for finite_hereditary_maximal_extension__p2m_3f244f53_8936_4715_8547_0063dd70ff12_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:40:17.972975+00:00
-- url     : https://prove2.me/submissions/66939b58-d1ee-49ea-a915-84e98e83a975

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (K : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hK : P K)
    (hdown : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ P H ∧
      ∀ J : SimpleGraph V, K ≤ J → P J → H ≤ J → J = H := by
  classical
  let p : SimpleGraph V → Prop := fun G => K ≤ G ∧ P G
  obtain ⟨H, hKH, hmax⟩ :=
    Finite.exists_le_maximal (a := K) (p := p) (show p K from ⟨le_rfl, hK⟩)
  rcases hmax with ⟨hpH, hmax⟩
  rcases hpH with ⟨_, hPH⟩
  refine ⟨H, hKH, hPH, ?_⟩
  intro J hKJ hPJ hHJ
  have hJ : p J := ⟨hKJ, hPJ⟩
  exact le_antisymm (hmax hJ hHJ) hHJ