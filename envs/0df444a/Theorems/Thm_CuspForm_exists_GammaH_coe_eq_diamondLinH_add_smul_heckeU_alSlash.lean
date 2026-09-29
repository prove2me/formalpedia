-- Prove2me | Theorems.Thm_CuspForm_exists_GammaH_coe_eq_diamondLinH_add_smul_heckeU_alSlash
-- name    : CuspForm.exists_GammaH_coe_eq_diamondLinH_add_smul_heckeU_alSlash
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/e5ee0a47-078b-5f11-8c8b-6a22704186a7
-- title:
--   Diamond-twisted level lowering from Γ_H(M) to Γ_{H'}(M/p)
-- statement:
--   Fix natural numbers $M$ (nonzero) and $p$ with $p$ prime, and an Atkin–Lehner datum $W$ at $(M,p)$: a level $R = W.R$ with $M = p\,R$ together with integers $a,b$ satisfying $pa - Rb = 1$. Let $H \le (\mathbb{Z}/M)^\times$ be a subgroup with the property that every unit of $\mathbb{Z}/M$ whose image under the reduction map $\mathtt{ZMod.unitsMap}$ to $(\mathbb{Z}/R)^\times$ is $1$ already lies in $H$, let $k \in \mathbb{Z}$, and let $F$ be a cusp form of weight $k$ for [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the subgroup of $SL_2(\mathbb{Z})$ consisting of the matrices of $\Gamma_0(M)$ whose lower-right entry reduces into $H$ modulo $M$. Let $d$ be a unit of $\mathbb{Z}/M$ whose image in $\mathbb{Z}/R$ is the class of $p$. Then there is a cusp form $G$ of weight $k$ for [`CohCarrier.GammaH W.R (H.map (ZMod.unitsMap …))`](def/CohCarrier_Level.html#L133), that is, for the group attached at level $R$ to the image $H'$ of $H$ in $(\mathbb{Z}/R)^\times$, whose underlying function $\mathbb{H} \to \mathbb{C}$ equals $$\langle d\rangle F + p^{2-k}\, U_p\bigl(F \mid_k W\bigr).$$ Here $\langle d\rangle F$ is [`CuspForm.diamondLinH k d F`](def/CuspForm_HeckeOperatorFormsGammaH.html#L132), the slash of $F$ by the image in $GL_2(\mathbb{R})$ of a lift `gammaLift M d` of $d$ to $SL_2(\mathbb{Z})$ (this linear operator is defined as $0$ unless the cusp-vanishing predicate [`CuspForm.StableD M H k`](def/CuspForm_HeckeOperatorFormsGammaH.html#L72) holds, which it always does); $F \mid_k W$ is [`ModularForm.alSlash W k ⇑F`](def/ModularForm_AtkinLehnerDatum.html#L141), the weight-$k$ slash of $F$ by the real matrix `W.alGL` attached to the datum, of determinant $p$; and $U_p$ is [`ModularForm.heckeU k p`](def/ModularForm_HeckeOperator.html#L93), the sum of the weight-$k$ slashes by the matrices $\begin{pmatrix}1 & j\\ 0 & p\end{pmatrix}$ for $0 \le j < p$.
--
--   This is the Atkin–Lehner level-lowering trace in its $\Gamma_H$ form: the combination $\langle d\rangle F + p^{2-k} U_p(F\mid_k W)$ descends from level $\Gamma_H(M)$ to level $\Gamma_{H'}(M/p)$, the diamond twist on the first term being needed because $W^2$ differs from $p$ times the identity by an element of $\Gamma_0(M)$ with lower-right entry congruent to $p$ modulo $M/p$. It is used in the integrality statements for $q$-expansion coefficients of the diamond and $U_p$ operators on $\Gamma_H$-cusp forms, and in the comparison of cusp forms with regular differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_GammaH_coe_eq_diamondLinH_add_smul_heckeU_alSlash.lean

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.exists_GammaH_coe_eq_diamondLinH_add_smul_heckeU_alSlash
    {M p : ℕ} [NeZero M] (hp : p.Prime) (W : ModularForm.AtkinLehnerDatum M p)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    (k : ℤ) (F : CuspForm (CohCarrier.GammaH M H) k)
    (d : (ZMod M)ˣ)
    (hd : (ZMod.unitsMap (Dvd.intro_left p W.hM.symm) d : ZMod W.R) = (p : ZMod W.R)) :
    ∃ G : CuspForm (CohCarrier.GammaH W.R (H.map (ZMod.unitsMap (Dvd.intro_left p W.hM.symm)))) k,
      ⇑G = ⇑(CuspForm.diamondLinH k d F) + (p : ℂ) ^ (2 - k) •
        ModularForm.heckeU k p (ModularForm.alSlash W k ⇑F) := by sorry
