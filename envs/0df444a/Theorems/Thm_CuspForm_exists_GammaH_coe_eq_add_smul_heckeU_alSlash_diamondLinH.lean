-- Prove2me | Theorems.Thm_CuspForm_exists_GammaH_coe_eq_add_smul_heckeU_alSlash_diamondLinH
-- name    : CuspForm.exists_GammaH_coe_eq_add_smul_heckeU_alSlash_diamondLinH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/542fbad3-b077-566a-9672-e174db81cae2
-- title:
--   Trace of a cusp form from Γ_H(M) to Γ_{H'}(M/p)
-- statement:
--   Let $M$ be a nonzero natural number, $p$ a prime, and let $W$ be an Atkin–Lehner datum for $(M,p)$: a natural number $R = W.R$ with $M = p\,R$ together with integers $a,b$ satisfying $pa - Rb = 1$. Write $\pi\colon(\mathbb{Z}/M)^\times \to (\mathbb{Z}/R)^\times$ for the reduction map coming from $R \mid M$. Let $H \le (\mathbb{Z}/M)^\times$ be a subgroup containing every unit $u$ with $\pi(u) = 1$, let $k \in \mathbb{Z}$, and let $F$ be a cusp form of weight $k$ for $\Gamma_H(M)$, the subgroup of $\mathrm{SL}(2,\mathbb{Z})$ obtained as the image under the inclusion $\Gamma_0(M)\hookrightarrow \mathrm{SL}(2,\mathbb{Z})$ of the matrices whose lower-right entry reduces into $H$, viewed inside $\mathrm{GL}(2,\mathbb{R})$. Let $d' \in (\mathbb{Z}/M)^\times$ satisfy $\pi(d')\cdot p = 1$ in $\mathbb{Z}/R$. Then there is a cusp form $G$ of weight $k$ for $\Gamma_{H'}(R)$, with $H' = \pi(H)$, such that as functions on the upper half-plane
--   $$G = F + p^{\,2-k}\,\sum_{j=0}^{p-1} \bigl(\,(\langle d'\rangle F)\bigm|_k W.alGL\,\bigr)\Bigm|_k \begin{pmatrix} 1 & j \\ 0 & p\end{pmatrix}.$$
--   Here $W.alGL$ is the real invertible matrix attached to the datum, of determinant $p$; $\langle d'\rangle F$ is [`CuspForm.diamondLinH k d' F`](def/CuspForm_HeckeOperatorFormsGammaH.html#L132), the slash of $F$ by a lift `gammaLift M d'` of $d'$ to $\mathrm{SL}(2,\mathbb{Z})$ (the branch condition [`CuspForm.StableD`](def/CuspForm_HeckeOperatorFormsGammaH.html#L72) in its definition holds by [`CuspForm.stableD`](thm.html#CuspForm.stableD)); and the inner sum is [`ModularForm.heckeU k p`](def/ModularForm_HeckeOperator.html#L93), the operator $U_p$.
--
--   This is the Atkin–Lehner trace identity expressing the trace of a cusp form from level $\Gamma_H(M)$ down to level $\Gamma_{H'}(M/p)$ in the shape $F + p^{2-k}U_p((\langle d'\rangle F)\mid W_p)$, with the main term untwisted. It is used in the derivation of congruences between the $q$-expansion coefficients of $F$ and those of a form of level $M/p$, namely by [`CuspForm.exists_forall_weight_add_mul_qCoeff_congr_gammaH_level_div_of_alSlash_diamondLinH_p_integral`](thm.html#CuspForm.exists_forall_weight_add_mul_qCoeff_congr_gammaH_level_div_of_alSlash_diamondLinH_p_integral).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_GammaH_coe_eq_add_smul_heckeU_alSlash_diamondLinH.lean

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

theorem CuspForm.exists_GammaH_coe_eq_add_smul_heckeU_alSlash_diamondLinH
    {M p : ℕ} [NeZero M] (hp : p.Prime) (W : ModularForm.AtkinLehnerDatum M p)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    (k : ℤ) (F : CuspForm (CohCarrier.GammaH M H) k)
    (d' : (ZMod M)ˣ)
    (hd' : (ZMod.unitsMap (Dvd.intro_left p W.hM.symm) d' : ZMod W.R) * (p : ZMod W.R) = 1) :
    ∃ G : CuspForm (CohCarrier.GammaH W.R (H.map (ZMod.unitsMap (Dvd.intro_left p W.hM.symm)))) k,
      ⇑G = ⇑F + (p : ℂ) ^ (2 - k) •
        ModularForm.heckeU k p (ModularForm.alSlash W k ⇑(CuspForm.diamondLinH k d' F)) := by sorry
