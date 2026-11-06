-- Prove2me | solution 1 for finite_maximal_extension_of_hereditary_property__p2m_3e187282_ed42_4b71_bc6a_a0a726731916_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T14:59:08.674118+00:00
-- url     : https://prove2.me/submissions/582674a6-4b78-46ed-be2d-5f6b7f887779

-- ID: 67bd6668-a3be-4f37-b3da-343480d288a1 | NAME: finite_maximal_extension_of_hereditary_property__p2m_3e187282_ed42_4b71_bc6a_a0a726731916_a1 | 未本地编译验证
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop)
    (hhered : ∀ ⦃A B : SimpleGraph V⦄, A ≤ B → P B → P A)
    (G : SimpleGraph V) (hG : P G) :
    ∃ R : SimpleGraph V, G ≤ R ∧ P R ∧
      ∀ H : SimpleGraph V, R ≤ H → P H → H = R := by
  classical
  obtain ⟨R, hGR, hmax⟩ :=
    Finite.exists_le_maximal (α := SimpleGraph V) (p := P) (a := G) hG
  rcases hmax with ⟨hPR, hmax'⟩
  refine ⟨R, hGR, hPR, ?_⟩
  intro H hRH hPH
  exact le_antisymm (hmax' hPH hRH) hRH
