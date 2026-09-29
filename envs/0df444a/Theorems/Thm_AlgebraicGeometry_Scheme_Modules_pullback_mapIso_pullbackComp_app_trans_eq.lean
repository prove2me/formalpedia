-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullback_mapIso_pullbackComp_app_trans_eq
-- name    : AlgebraicGeometry.Scheme.Modules.pullback_mapIso_pullbackComp_app_trans_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/a3d26b07-9a47-54f2-91c0-279a8e81903d
-- title:
--   Pullback pseudofunctor coherence along a commuting ladder
-- statement:
--   Let $T_3,T_2,T_1,X_3,A'',A'$ be schemes (in a fixed universe) and let $e_3:T_3\to X_3$, $b:X_3\to A''$, $s:T_3\to T_2$, $e'':T_2\to A''$, $a:A''\to A'$, $i:T_2\to T_1$, $e':T_1\to A'$ be morphisms of schemes, subject to the commutativity hypotheses $hb: e_3\circ b = s\circ e''$ (in diagrammatic order, $e_3$ followed by $b$ equals $s$ followed by $e''$), $ha: e''\circ a = i\circ e'$ and $hk: e_3\circ(b\circ a) = (s\circ i)\circ e'$; the last is a consequence of the first two but is taken as a separate hypothesis, so that only the equation, not a particular proof of it, enters. Let $L$ be a sheaf of modules on $A'$. The assertion is an equality of two isomorphisms $e_3^*b^*a^*L \cong (s\circ i)^*e'^*L$ in the category of sheaves of modules on $T_3$. The first is obtained by applying $e_3^*$ to the comparison $b^*a^*L\cong(b\circ a)^*L$, then composing $e_3^*(b\circ a)^*L\cong(e_3\circ b\circ a)^*L$, the transport along $hk$, and the inverse of $(s\circ i)^*e'^*L\cong((s\circ i)\circ e')^*L$. The second runs along the other side of the ladder: $e_3^*b^*(a^*L)\cong(e_3\circ b)^*(a^*L)$, transport along $hb$, the inverse of $(s\circ e'')^*(a^*L)\cong s^*e''^*(a^*L)$, then $s^*$ applied to the analogous composite built from $ha$, and finally $s^*i^*(e'^*L)\cong(s\circ i)^*(e'^*L)$.
--
--   This is a coherence statement for the pullback pseudofunctor on sheaves of modules over schemes: the two evident ways of comparing $e_3^*b^*a^*L$ with $(s\circ i)^*e'^*L$ across a commuting ladder of schemes agree. It is used in [`AlgebraicGeometry.Polarisation.cocycle_of_rigidifiedIso`](thm.html#AlgebraicGeometry.Polarisation.cocycle_of_rigidifiedIso), where two descriptions of a descent datum on triple overlaps must be identified.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_pullback_mapIso_pullbackComp_app_trans_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.pullback_mapIso_pullbackComp_app_trans_eq
    {T₃ T₂ T₁ X₃ A'' A' : Scheme.{u}} (e₃ : T₃ ⟶ X₃) (b : X₃ ⟶ A'') (s : T₃ ⟶ T₂) (e'' : T₂ ⟶ A'')
    (a : A'' ⟶ A') (i : T₂ ⟶ T₁) (e' : T₁ ⟶ A') (hb : e₃ ≫ b = s ≫ e'') (ha : e'' ≫ a = i ≫ e')
    (hk : e₃ ≫ b ≫ a = (s ≫ i) ≫ e') (L : A'.Modules) :
    (Scheme.Modules.pullback e₃).mapIso ((Scheme.Modules.pullbackComp b a).app L) ≪≫
        ((Scheme.Modules.pullbackComp e₃ (b ≫ a)).app L ≪≫ (Scheme.Modules.pullbackCongr hk).app L ≪≫
          ((Scheme.Modules.pullbackComp (s ≫ i) e').app L).symm) =
      ((Scheme.Modules.pullbackComp e₃ b).app ((Scheme.Modules.pullback a).obj L) ≪≫
          (Scheme.Modules.pullbackCongr hb).app ((Scheme.Modules.pullback a).obj L) ≪≫
          ((Scheme.Modules.pullbackComp s e'').app ((Scheme.Modules.pullback a).obj L)).symm) ≪≫
        (Scheme.Modules.pullback s).mapIso
          ((Scheme.Modules.pullbackComp e'' a).app L ≪≫ (Scheme.Modules.pullbackCongr ha).app L ≪≫
            ((Scheme.Modules.pullbackComp i e').app L).symm) ≪≫
        (Scheme.Modules.pullbackComp s i).app ((Scheme.Modules.pullback e').obj L) := by sorry
