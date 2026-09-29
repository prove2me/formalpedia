-- Prove2me | Theorems.Thm_CuspForm_IsNewform_sum_range_slash_heckeDiagMatrix_conj_eq_qCoeff_smul
-- name    : CuspForm.IsNewform.sum_range_slash_heckeDiagMatrix_conj_eq_qCoeff_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/310723db-cc47-51e2-8e2a-179d54f0f37a
-- title:
--   Trace of f∣ D_q over Γ₀(qN₀)-cosets equals a_q f
-- statement:
--   Let $N$, $N_0$ and $q$ be natural numbers and let $f$ be a cusp form of weight $2$ for $\Gamma_0(N)$ which is a newform in the sense of the project: $f$ is a normalised eigenform, meaning that its $q$-expansion coefficients $a_n(f) =$ `qCoeff f n` (the $n$-th coefficient of the $q$-expansion of $f$ with width $1$) satisfy $a_1(f) = 1$, $a_{mn}(f) = a_m(f)a_n(f)$ for coprime $m,n$, $a_{p^{r+2}}(f) = a_p(f)a_{p^{r+1}}(f) - p\,a_{p^r}(f)$ for primes $p \nmid N$ and $a_{p^{r+2}}(f) = a_p(f)a_{p^{r+1}}(f)$ for primes $p \mid N$; and, for every proper divisor $M$ of $N$, no normalised eigenform of weight $2$ on $\Gamma_0(M)$ has the same coefficients as $f$ at all primes not dividing $N$. Assume further that $q$ is prime, that $q N_0 = N$ and that $q \nmid N_0$, so $q$ divides $N$ exactly once (in particular $N_0 \neq 0$, hence $N \neq 0$). Write $D_q$ for [`ModularForm.heckeDiagMatrix q`](def/ModularForm_HeckeOperator.html#L21), the element of $\mathrm{GL}_2(\mathbb{R})$ given by $\bigl(\begin{smallmatrix} q & 0 \\ 0 & 1\end{smallmatrix}\bigr)$ when $q \neq 0$. Then, as an identity of functions on the upper half-plane, with all slashes taken in weight $2$, $$\sum_{j=0}^{q-1} \bigl(f \mid D_q\bigr) \;\Big|\; \bigl(S\, T^{-Nj}\, S^{-1}\bigr) \;=\; a_q(f)\cdot f ,$$ where $S$ and $T$ are the standard generators of the modular group, so that $S T^{-Nj} S^{-1} = \bigl(\begin{smallmatrix} 1 & 0 \\ Nj & 1\end{smallmatrix}\bigr)$.
--
--   The matrices $\bigl(\begin{smallmatrix} 1 & 0 \\ Nj & 1\end{smallmatrix}\bigr)$, $0 \le j < q$, run through a transversal of $\Gamma_0(qN)$ in $\Gamma_0(N)$, so the left-hand side is the trace back to level $N$ of the form $f$ slashed by $\mathrm{diag}(q,1)$; the identity computes this trace as the $q$-th Hecke eigenvalue of $f$, the newform hypothesis being what makes the answer a scalar multiple of $f$. It rests on the Atkin–Lehner relations in weight $2$ and on the vanishing of the Atkin–Lehner trace on newforms, and is used in the construction of the level-raising congruence via [`CuspForm.IsNewform.rescaleLin_sub_rescaleLin_notMem_span_sup_span`](thm.html#CuspForm.IsNewform.rescaleLin_sub_rescaleLin_notMem_span_sup_span).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNewform_sum_range_slash_heckeDiagMatrix_conj_eq_qCoeff_smul.lean

import Definitions.Def_CuspForm_Newforms
import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped ModularForm MatrixGroups in

theorem CuspForm.IsNewform.sum_range_slash_heckeDiagMatrix_conj_eq_qCoeff_smul
    {N N₀ q : ℕ} {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : CuspForm.IsNewform f)
    (hq : q.Prime) (hqN : q * N₀ = N) (hqN₀ : ¬ q ∣ N₀) :
    ∑ j ∈ Finset.range q,
      (⇑f ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q)
        ∣[(2 : ℤ)] (ModularGroup.S * ModularGroup.T ^ (-((N * j : ℕ) : ℤ)) * ModularGroup.S⁻¹)
      = (ModularFormClass.qCoeff f q) • ⇑f := by sorry
