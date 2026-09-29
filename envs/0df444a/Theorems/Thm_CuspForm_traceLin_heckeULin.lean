-- Prove2me | Theorems.Thm_CuspForm_traceLin_heckeULin
-- name    : CuspForm.traceLin_heckeULin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/f3a0e8e6-a20b-5f49-828d-96c74d5923c5
-- title:
--   Level-lowering trace commutes with U_ℓ, ℓ≠ q
-- statement:
--   Let $M$ and $q$ be natural numbers with $M$ nonzero, and let $A$ be an Atkin–Lehner datum for $(M,q)$, that is, a natural number $R = A.R$ together with the factorisation $M = qR$ and integers $a,b$ satisfying $qa - Rb = 1$; assume $q$ is prime. Let $\ell$ be a prime with $\ell \mid M$ and $\ell \mid R$, and assume $\ell \ne q$. For a cusp form $f$ of weight $2$ on $\Gamma_0(M)$, write $U_\ell$ for the operator induced on weight-$2$ cusp forms by $g \mapsto \sum_{j<\ell} g \mid_2 \mathrm{heckeMatrix}\,\ell\,j$ (at level $M$ via $\ell \mid M$, at level $R$ via $\ell \mid R$), and write $\operatorname{Tr}$ for the linear map [`CuspForm.traceLin`](def/CuspForm_LevelLoweringTrace.html#L18) from weight-$2$ cusp forms on $\Gamma_0(M)$ to weight-$2$ cusp forms on $\Gamma_0(R)$ whose underlying function is $g \mapsto g + U_q\bigl(g \mid_2 A.\mathrm{alGL}\bigr)$, the slash being by the Atkin–Lehner matrix attached to $A$. The assertion is the identity $\operatorname{Tr}(U_\ell f) = U_\ell(\operatorname{Tr} f)$ in weight-$2$ cusp forms on $\Gamma_0(R)$, the right-hand $U_\ell$ being the level-$R$ operator.
--
--   This is the compatibility, classical in the Atkin–Lehner theory of newforms, of the trace map $S_2(\Gamma_0(qR)) \to S_2(\Gamma_0(R))$ attached to $w_q$ with the Hecke operator $U_\ell$ at a bad prime $\ell \ne q$. It is used in showing that the $q$-new condition behaves well under the Hecke operators away from $q$, feeding into the construction of normalised eigenforms new at a prescribed set of primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_traceLin_heckeULin.lean

import Mathlib
import Definitions.Def_CuspForm_LevelLoweringTrace
import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.traceLin_heckeULin {M q : ℕ} [NeZero M] (A : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ℓ ∣ M) (hℓR : ℓ ∣ A.R) (hne : ℓ ≠ q) (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    haveI : NeZero A.R := ⟨A.R_pos.ne'⟩
    CuspForm.traceLin A hq (CuspForm.heckeULin 2 hℓM f) = CuspForm.heckeULin 2 hℓR (CuspForm.traceLin A hq f) := by sorry
