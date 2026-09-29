-- Prove2me | Theorems.Thm_CuspForm_sum_slash_map_inv_slash_heckeDiagMatrix_eq_coe_heckeTLinH
-- name    : CuspForm.sum_slash_map_inv_slash_heckeDiagMatrix_eq_coe_heckeTLinH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/b3d5119d-c63b-5b0a-b8da-b1da1fd2ab1e
-- title:
--   Full-level Hecke sum transports to T_ℓ on Γ_H(q²M')
-- statement:
--   Fix a prime $q$, an integer $M'\neq 0$ and a prime $\ell$ with $\ell\nmid q^2M'$. Let $t:\{0,\dots,\ell-1\}\to\mathbb Z$ satisfy $q\mid t_i$ for all $i$ and $i\mapsto t_i \bmod \ell$ injective, and let $\gamma_i\in \mathrm{GL}_2(\mathbb Q)$ have underlying matrix $!![\ell,t_i;0,1]$. Let $\sigma\in\mathrm{SL}_2(\mathbb Z)$ satisfy $q\mid \sigma_{01}$, $qM'\ell\mid\sigma_{10}$ and $\sigma_{00}\equiv\ell \pmod q$, and let $\gamma_\infty\in\mathrm{GL}_2(\mathbb Q)$ have underlying matrix $\sigma\cdot !![1,0;0,\ell]$ (entries of $\sigma$ cast to $\mathbb Q$). Let $f:\mathbb H\to\mathbb C$ be any function and let $F'$ be a weight-$2$ cusp form for [`CohCarrier.GammaH`](def/CohCarrier_Level.html#L133) $(q^2M')$ $(\mathrm{levelH}\,q\,M')$, i.e. for the image in $\mathrm{SL}_2(\mathbb Z)$ of those elements of $\Gamma_0(q^2M')$ whose lower-right entry reduces into the kernel of $(\mathbb Z/q^2M')^\times\to(\mathbb Z/q)^\times$, and assume $F' = f\mid_2 \mathrm{diag}(q,1)$, where $\mathrm{diag}(q,1)$ is [`ModularForm.heckeDiagMatrix`](def/ModularForm_HeckeOperator.html#L21) $q$. Then $$\Bigl(\sum_{i} f\mid_2\gamma_i^{-1} \;+\; f\mid_2\gamma_\infty^{-1}\Bigr)\Big|_2 \mathrm{diag}(q,1) \;=\; \mathrm{heckeTLinH}\,2\,h_\ell\,h_{\ell N}\,(F'),$$ the $\gamma_i^{-1},\gamma_\infty^{-1}$ being mapped into $\mathrm{GL}_2(\mathbb R)$ along $\mathbb Q\hookrightarrow\mathbb R$. Here [`CuspForm.heckeTLinH`](def/CuspForm_HeckeOperatorFormsGammaH.html#L224) is, since [`CuspForm.stableT`](thm.html#CuspForm.stableT) gives the predicate `StableT`, the $\mathbb C$-linear operator $F\mapsto \mathrm{heckeU}\,2\,\ell\,F + F\mid_2\bigl(\mathrm{gammaLift}(\ell)\cdot \mathrm{diag}(\ell,1)\bigr)$.
--
--   This is the compatibility that identifies the classical Hecke operator $T_\ell$ on weight-two cusp forms of level $\Gamma_H(q^2M')$ with an explicit sum of weight-two slash operators by the full-level coset representatives $\gamma_i,\gamma_\infty$, conjugated by $\mathrm{diag}(q,1)$. It is used in the computation of the action of $T_\ell$ on adelic lifts of newforms, in [`CuspForm.IsAdelicLiftOf.heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform`](thm.html#CuspForm.IsAdelicLiftOf.heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_sum_slash_map_inv_slash_heckeDiagMatrix_eq_coe_heckeTLinH.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups ModularForm

theorem CuspForm.sum_slash_map_inv_slash_heckeDiagMatrix_eq_coe_heckeTLinH
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ q ^ 2 * M')
    (t : Fin ℓ → ℤ) (htq : ∀ i, (q : ℤ) ∣ t i) (htℓ : Function.Injective fun i => ((t i : ℤ) : ZMod ℓ))
    (γ : Fin ℓ → GL (Fin 2) ℚ)
    (hγ : ∀ i, ((γ i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![(ℓ : ℚ), (t i : ℚ); 0, 1])
    (σ : SL(2, ℤ)) (hσb : (q : ℤ) ∣ σ 0 1) (hσc : ((q * M' * ℓ : ℕ) : ℤ) ∣ σ 1 0)
    (hσa : ((σ 0 0 : ℤ) : ZMod q) = (ℓ : ZMod q))
    (γinf : GL (Fin 2) ℚ)
    (hγinf : ((γinf : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) * !![1, 0; 0, (ℓ : ℚ)])
    (f : UpperHalfPlane → ℂ)
    (F' : CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2)
    (hF' : ⇑F' = f ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q) :
    ((∑ i, f ∣[(2 : ℤ)] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (γ i)⁻¹) +
        f ∣[(2 : ℤ)] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γinf⁻¹) ∣[(2 : ℤ)]
        ModularForm.heckeDiagMatrix q =
      ⇑(CuspForm.heckeTLinH 2 hℓ hℓN F') := by sorry
