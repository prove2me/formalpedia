-- Prove2me | Theorems.Thm_CuspForm_traceLin_atkinLehnerLin_eq_zero_of_isNewform
-- name    : CuspForm.traceLin_atkinLehnerLin_eq_zero_of_isNewform
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/92d8bf9e-dc72-52c5-8627-a6a4f88733f0
-- title:
--   Level-lowering trace annihilates w_q f for a newform
-- statement:
--   Let $N$ and $q$ be natural numbers with $N \neq 0$, and let $W$ be an Atkin–Lehner datum for $(N,q)$: a natural number $R = W.R$ together with the relation $N = qR$ and integers $a, b$ satisfying $qa - Rb = 1$ (so $q$ and $R$ are coprime). Let $q$ be prime, and let $f$ be a weight-$2$ cusp form on $\Gamma_0(N)$ which is a newform in the sense of [`CuspForm.IsNewform`](def/CuspForm_Newforms.html#L23), i.e. $f$ is a normalised eigenform — its $q$-expansion coefficients satisfy $a_1(f) = 1$, multiplicativity $a_{mn}(f) = a_m(f)a_n(f)$ for coprime $m, n$, the recursion $a_{p^{r+2}}(f) = a_p(f)a_{p^{r+1}}(f) - p\,a_{p^r}(f)$ for primes $p \nmid N$ and $a_{p^{r+2}}(f) = a_p(f)a_{p^{r+1}}(f)$ for $p \mid N$ — and moreover for no divisor $M$ of $N$ with $M \neq N$ does there exist a normalised eigenform $g$ of weight $2$ on $\Gamma_0(M)$ with $a_\ell(g) = a_\ell(f)$ for all primes $\ell \nmid N$. The conclusion is that $\mathrm{Tr}(w_q f) = 0$ in $S_2(\Gamma_0(R))$, where $w_q f$ is the cusp form with underlying function $f \mid_2 W.\mathrm{alGL}$ and $\mathrm{Tr}(g)$ is the cusp form on $\Gamma_0(R)$ with underlying function $g + U_q(g \mid_2 W.\mathrm{alGL})$.
--
--   This is the newform/oldform orthogonality step at the prime $q$ exactly dividing the level: the trace from level $N = qR$ down to level $R$ kills the Atkin–Lehner translate of a newform. It is used to identify the action of the Atkin–Lehner involution on a newform, in particular in [`CuspForm.atkinLehnerLin_eq_neg_qCoeff_smul_of_isNewform`](thm.html#CuspForm.atkinLehnerLin_eq_neg_qCoeff_smul_of_isNewform) and in the consequences drawn from it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_traceLin_atkinLehnerLin_eq_zero_of_isNewform.lean

import Mathlib
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Definitions.Def_CuspForm_LevelLoweringTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.traceLin_atkinLehnerLin_eq_zero_of_isNewform {N q : ℕ} [NeZero N]
    (W : ModularForm.AtkinLehnerDatum N q) (hq : q.Prime)
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNewform) :
    CuspForm.traceLin W hq (CuspForm.atkinLehnerLin W 2 f) = 0 := by sorry
