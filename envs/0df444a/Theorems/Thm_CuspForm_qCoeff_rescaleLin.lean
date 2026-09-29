-- Prove2me | Theorems.Thm_CuspForm_qCoeff_rescaleLin
-- name    : CuspForm.qCoeff_rescaleLin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/342ccbc3-4ee9-5397-874c-962e09ae32ce
-- title:
--   q-coefficients of the rescaling map V_d on cusp forms
-- statement:
--   Let $d$, $R$, $M$ be natural numbers with $M$ nonzero and $d\,R \mid M$, let $k$ be an integer, and let $f$ be a cusp form of weight $k$ for the image of $\Gamma_0(R)$ in $\mathrm{GL}_2(\mathbb{R})$. The map [`FreyPackage.ModMCarrier.rescaleLin hdRM k`](def/FreyPackage_ModMCarrier_Rescale.html#L140) is the $\mathbb{C}$-linear map from cusp forms of weight $k$ on $\Gamma_0(R)$ to cusp forms of weight $k$ on $\Gamma_0(M)$ whose underlying function is the weight-$k$ slash $f \mid_k \mathrm{heckeDiagMatrix}\,d$, where $\mathrm{heckeDiagMatrix}\,d$ is the identity when $d = 0$ and otherwise the invertible upper triangular real matrix $\begin{pmatrix} d & 0 \\ 0 & 1\end{pmatrix}$; the invariance, holomorphy and vanishing-at-cusps conditions for the target level are part of that construction. Writing $\mathrm{qCoeff}\,g\,n$ for the $n$-th coefficient of the $q$-expansion of $g$ at $\infty$ taken with period $1$, the assertion is that for every natural number $n$, $$\mathrm{qCoeff}\,\bigl(\mathrm{rescaleLin}\,f\bigr)\,n = \begin{cases} d^{\,k-1}\,\mathrm{qCoeff}\,f\,(n/d) & \text{if } d \mid n,\\ 0 & \text{otherwise,}\end{cases}$$ the exponent $k-1$ being an integer power of the complex number $d$ and $n/d$ natural division (exact in the relevant branch).
--
--   This is the classical formula for the $q$-expansion of the degeneracy (level-raising) operator $V_d$, $f \mapsto d^{k-1} f(d\tau)$, which sends $S_k(\Gamma_0(R))$ into $S_k(\Gamma_0(M))$ whenever $dR \mid M$. It is used in the project wherever $q$-coefficients of rescaled forms must be computed, for instance in the analysis of normalized eigenforms and of the Hecke action at primes where the relevant local behaviour is not unramified.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_qCoeff_rescaleLin.lean

import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CongruenceSubgroup

theorem CuspForm.qCoeff_rescaleLin
    {d R M : ℕ} [NeZero M] (hdRM : d * R ∣ M) (k : ℤ)
    (f : CuspForm (Gamma0 R) k) (n : ℕ) :
    ModularFormClass.qCoeff (FreyPackage.ModMCarrier.rescaleLin hdRM k f) n
      = if d ∣ n then (d : ℂ) ^ (k - 1) * ModularFormClass.qCoeff f (n / d) else 0 := by sorry
