-- Prove2me | Theorems.Thm_CuspForm_traceLin_rescaleLin
-- name    : CuspForm.traceLin_rescaleLin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/166f1dfc-e304-5180-9aff-e44ee9f60d5f
-- title:
--   Trace of the rescaling equals T_{q'}
-- statement:
--   Let $M$ and $q'$ be natural numbers with $M \neq 0$, and let $W$ be an Atkin–Lehner datum for the pair $(M,q')$: a level $R = W.R$ together with the factorisation $M = q' \cdot R$ and integers $a,b$ satisfying $q'a - Rb = 1$. Assume $q'$ is prime and $q' \nmid R$ (which in particular forces $R \neq 0$), and let $f$ be a weight-$2$ cusp form for $\Gamma_0(R)$. The assertion is the equality, in the space of weight-$2$ cusp forms for $\Gamma_0(R)$, $$\mathrm{traceLin}\,W\;\bigl(\mathrm{rescaleLin}\,f\bigr) = \mathrm{heckeTLin}\,f .$$ Here `rescaleLin`, applied with the divisibility $q' \cdot R \mid M$ coming from the datum, sends $f$ to the weight-$2$ cusp form on $\Gamma_0(M)$ whose underlying function is $f \mid[2] \mathrm{heckeDiagMatrix}\,q'$, the slash by $\begin{pmatrix} q' & 0\\ 0 & 1\end{pmatrix}$; `traceLin W` sends a weight-$2$ cusp form $g$ on $\Gamma_0(M)$ to the weight-$2$ cusp form on $\Gamma_0(R)$ with underlying function $g + U_{q'}\bigl(g \mid[2] W.\mathrm{alGL}\bigr)$, where $U_{q'}h = \sum_{j<q'} h\mid[2]\mathrm{heckeMatrix}\,q'\,j$; and `heckeTLin` is the linear operator on weight-$2$ cusp forms for $\Gamma_0(R)$ induced by $T_{q'}h = U_{q'}h + h\mid[2]\mathrm{heckeDiagMatrix}\,q'$.
--
--   This is the classical computation of the trace from level $M = q'R$ down to level $R$ of the degeneracy map $V_{q'}$ at a prime $q'$ not dividing $R$, giving $\operatorname{Tr}^M_R(V_{q'}f) = T_{q'}f$; it is one entry of the matrix of the trace on the two degeneracy embeddings used in level lowering. It is cited in the computation of $\sum_{j<q'}$ slashes of conjugates of $\mathrm{heckeDiagMatrix}\,q'$ for weight-$2$ cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_traceLin_rescaleLin.lean

import Definitions.Def_FreyPackage_ModMCarrier_OldSublattice
import Definitions.Def_CuspForm_LevelLoweringTrace
import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CongruenceSubgroup ModularForm FreyPackage.ModMCarrier

theorem CuspForm.traceLin_rescaleLin {M q' : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q') (hq : q'.Prime) (hqR : ¬ q' ∣ W.R)
    (f : CuspForm (Gamma0 W.R) 2) :
    haveI : NeZero W.R := ⟨fun h => absurd (h ▸ Nat.dvd_zero q') hqR⟩
    CuspForm.traceLin W hq (rescaleLin W.q_mul_R_dvd 2 f)
      = CuspForm.heckeTLin 2 hq hqR f := by sorry
