-- Prove2me | Theorems.Thm_CuspForm_exists_gamma1_coe_eq_alSlash_diamondLinH
-- name    : CuspForm.exists_gamma1_coe_eq_alSlash_diamondLinH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/ab40c802-527e-53b5-8088-16c1aa268e81
-- title:
--   Atkin–Lehner translate of a diamond operator on Γ₁(M)
-- statement:
--   Fix a prime $p$ and a nonzero level $M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and assume $p \mid M$ and $p^2 \nmid M$. Let $W_d$ be an Atkin–Lehner datum for the pair $(M, M/p)$, that is, a cofactor $R$ with $M = (M/p)\cdot R$ together with integers $a,b$ satisfying $(M/p)a - Rb = 1$; let $e \in (\mathbb{Z}/M)^\times$, and let $f$ be a weight-two cusp form for the group $\Gamma_H(M) \le \mathrm{SL}_2(\mathbb{Z})$, defined as the image under the inclusion $\Gamma_0(M) \hookrightarrow \mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the homomorphism $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$ recording the lower-right entry. Assume further that $f$ lies in the two-cusp integrality set at $p$ for the smallest subring $\bot \subseteq \mathbb{C}$, i.e. for every element $t$ of the Hecke subring `heckeRingH`, every Atkin–Lehner datum $W$ for $(M,p)$ and every $n$, the $n$-th $q$-expansion coefficients of $t f$ and of $(tf)\mid_2 W$ lie in $\bot$. The conclusion is that there is a weight-two cusp form $g$ for $\Gamma_1(M)$ whose underlying function $\mathbb{H} \to \mathbb{C}$ equals the weight-two slash of the function of $\langle e\rangle f$ by the image in $GL_2(\mathbb{R})$ of the matrix attached to $W_d$; here $\langle e \rangle f$ is `diamondLinH 2 e f`, the slash of $f$ by a lift of $e$ when the cusp-stability predicate `StableD M H 2` holds, and $0$ otherwise. The proof visibly discards the hypotheses $p \mid M$, $p^2 \nmid M$ and the integrality hypothesis on $f$.
--
--   This records that the Atkin–Lehner translate at $q = M/p$ of a diamond-operator translate of a weight-two cusp form on $\Gamma_H(M)$ is again (the underlying function of) a cusp form on $\Gamma_1(M)$, the level at which the Atkin–Lehner involution is available without any compatibility condition between $H$ and $p$. It feeds the integrality and non-divisibility statement for $q$-expansions of Atkin–Lehner translates of diamond translates used further on.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_gamma1_coe_eq_alSlash_diamondLinH.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem CuspForm.exists_gamma1_coe_eq_alSlash_diamondLinH
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (Wd : ModularForm.AtkinLehnerDatum M (M / p)) (e : (ZMod M)ˣ)
    (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma1 M) 2, (⇑g : UpperHalfPlane → ℂ) = ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f) := by sorry
