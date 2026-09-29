-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_ofScalar_act
-- name    : AlgebraicGeometry.Polarisation.ThetaPt.ofScalar_act
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/ed67553b-abaa-5beb-8d20-cf855ec7ea92
-- title:
--   Scalar theta points act by the corresponding base scalar
-- statement:
--   Fix a commutative ring $S$, a scheme $A$, a morphism $f : A \to \operatorname{Spec} S$, and a `RelativeGroupLaw` $L$ for $f$, that is, a group structure (multiplication, unit, inverse, with associativity, the two unit laws, left inverse law, and naturality under base change along morphisms $\psi$ with $\psi$ followed by $t$ equal to $t'$) on the sets of $T$-points $\{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$, functorially in $t : T \to \operatorname{Spec} S$. Fix furthermore an $A$-module object $\mathcal{L}$, a commutative ring $R$, and a morphism $t : \operatorname{Spec} R \to \operatorname{Spec} S$, write $A_R = A \times_{\operatorname{Spec} S} \operatorname{Spec} R$ and $\mathcal{L}_R$ for the pullback of $\mathcal{L}$ along the first projection. Then for a unit $c \in R^\times$ and a global section $s$ of $\mathcal{L}_R$, the theta point `ThetaPt.ofScalar c` acts on $s$ by multiplication by the global function `baseScalar f t c` on $A_R$, namely the image of $c$ under the inverse of the canonical isomorphism $\Gamma(\operatorname{Spec} R, \mathcal{O}) \cong R$ followed by the second projection $A_R \to \operatorname{Spec} R$ on global functions. Here `ThetaPt.ofScalar c` is the theta point whose underlying point is the unit section $L.\mathrm{one}\ t$ and whose isomorphism is the canonical identification of the pullback of $\mathcal{L}_R$ along translation by the unit section with $\mathcal{L}_R$, followed by the homothety by the unit `baseScalar f t c`; and the action of a theta point $\theta$ sends $s$ to the value of $\theta.\mathrm{iso}$ on the canonical pullback section of $s$ along the translation by $\theta.\mathrm{pt}$.
--
--   This identifies the action of the central, scalar theta points: those coming from units of the base ring act on sections of $\mathcal{L}_R$ simply by the corresponding global function on $A_R$. It is used in the analysis of Schrödinger frames and of level lifts, where frames are compared modulo the scalars $R^\times$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_ThetaPt_ofScalar_act.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.ThetaPt.ofScalar_act
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} {L : RelativeGroupLaw S f}
    {𝓛 : A.Modules} {R : Type} [CommRing R] {t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)}
    (c : Rˣ) (s : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤)) :
    (ThetaPt.ofScalar c : ThetaPt f L 𝓛 t).act s = baseScalar f t c • s := by sorry
