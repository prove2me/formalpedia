-- Prove2me | Theorems.Thm_CuspForm_heckeTLin_rescaleLin
-- name    : CuspForm.heckeTLin_rescaleLin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/f089622c-643e-5138-84eb-b8c850c3d937
-- title:
--   Hecke operators at ℓ commute with degeneracy rescaling
-- statement:
--   Let $R$, $M$, $d$, $\ell$ be natural numbers with $M \neq 0$, and assume $dR \mid M$, that $\ell$ is prime, that $\ell \nmid M$ and that $\ell \nmid R$. Let $f$ be a cusp form of weight $2$ for $\Gamma_0(R)$. Here [`FreyPackage.ModMCarrier.rescaleLin hdRM 2`](def/FreyPackage_ModMCarrier_Rescale.html#L140) is the $\mathbb{C}$-linear map from weight-$2$ cusp forms on $\Gamma_0(R)$ to weight-$2$ cusp forms on $\Gamma_0(M)$ whose underlying function is the slash action $f \mapsto f \mid_{2} \mathrm{heckeDiagMatrix}\, d$, where $\mathrm{heckeDiagMatrix}\, d$ is the matrix $\mathrm{diag}(d,1) \in \mathrm{GL}_2(\mathbb{R})$ for $d \neq 0$ (and the identity for $d = 0$); in weight $2$ this is $\tau \mapsto d\, f(d\tau)$. The map [`CuspForm.heckeTLin 2 hℓ hℓN`](def/ModularForm_HeckeOperatorForms.html#L69) is the $\mathbb{C}$-linear endomorphism of weight-$2$ cusp forms on $\Gamma_0(N)$ whose underlying function is $\mathrm{heckeT}\,2\,\ell\,f = \mathrm{heckeU}\,2\,\ell\,f + f \mid_{2} \mathrm{heckeDiagMatrix}\,\ell$. The assertion is that applying the operator at $\ell$ on level $M$ to the rescaling of $f$ gives the same weight-$2$ cusp form on $\Gamma_0(M)$ as rescaling the result of applying the operator at $\ell$ on level $R$ to $f$.
--
--   This is the compatibility of the Hecke operator $T_\ell$, at a prime $\ell$ good for the larger level, with the degeneracy map of index $d$ from level $R$ to level $M$. It is used in the study of newforms and their Hecke eigenvalues at level $M$, for instance in identifying eigenspaces for the operators $T_\ell$ and in transporting eigenvalue information between levels.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_heckeTLin_rescaleLin.lean

import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.heckeTLin_rescaleLin {R M d ℓ : ℕ} [NeZero M] (hdRM : d * R ∣ M)
    (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓR : ¬ ℓ ∣ R)
    (f : CuspForm (CongruenceSubgroup.Gamma0 R) 2) :
    CuspForm.heckeTLin 2 hℓ hℓM (FreyPackage.ModMCarrier.rescaleLin hdRM 2 f)
      = FreyPackage.ModMCarrier.rescaleLin hdRM 2 (CuspForm.heckeTLin 2 hℓ hℓR f) := by sorry
