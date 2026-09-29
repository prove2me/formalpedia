-- Prove2me | Theorems.Thm_CuspForm_sum_range_slash_heckeDiagMatrix_heckeDiagMatrix_conj_eq
-- name    : CuspForm.sum_range_slash_heckeDiagMatrix_heckeDiagMatrix_conj_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/ded4a8fa-2fa3-53a4-9401-1d997b86f4ab
-- title:
--   Lower-unipotent coset sum of the doubly q-rescaled cusp form
-- statement:
--   Let $N,q$ be natural numbers, let $f$ be a cusp form of weight $2$ for $\Gamma_0(N)$ (so that its underlying function on the upper half-plane is the object acted on below), and assume $q$ is prime and $q \nmid N$. Write $\mid[2]$ for the weight-$2$ slash action of $\mathrm{GL}_2(\mathbb{R})$, let $D_q =$ [`ModularForm.heckeDiagMatrix q`](def/ModularForm_HeckeOperator.html#L21) be the invertible matrix $\begin{pmatrix} q & 0 \\ 0 & 1\end{pmatrix}$ (the unit matrix when $q = 0$), and let $S$, $T$ be the standard generators `ModularGroup.S`, `ModularGroup.T`. The assertion is the identity of functions on the upper half-plane $$\sum_{j=0}^{q-1} \bigl((f \mid[2] D_q) \mid[2] D_q\bigr) \Bigm|[2]\; S\, T^{-qNj}\, S^{-1} \;=\; \bigl(T_q f\bigr)\mid[2] D_q \;-\; f,$$ where the exponent of $T$ is the integer $-(qNj)$ obtained from the natural number $qNj$, and where $T_q f =$ [`ModularForm.heckeT 2 q f`](def/ModularForm_HeckeOperator.html#L96) is by definition $\sum_{j<q} f \mid[2]\,$[`ModularForm.heckeMatrix q j`](def/ModularForm_HeckeOperator.html#L18) $\; + \; f \mid[2] D_q$, the weight-$2$ Hecke operator at $q$ written as the sum of the coset contributions [`ModularForm.heckeMatrix q j`](def/ModularForm_HeckeOperator.html#L18) together with the contribution of $D_q$.
--
--   The left-hand side is the trace, from level $q^2N$ down to level $qN$, of the cusp form obtained from $f$ by rescaling twice by $\operatorname{diag}(q,1)$: the matrices $S T^{-qNj} S^{-1} = \begin{pmatrix} 1 & 0 \\ qNj & 1\end{pmatrix}$, $0 \le j < q$, serve as a transversal for the relevant pair of congruence subgroups. The identity is the computational heart of the level-raising comparison used in [`CuspForm.IsNewform.rescaleLin_sub_rescaleLin_notMem_span_sup_span`](thm.html#CuspForm.IsNewform.rescaleLin_sub_rescaleLin_notMem_span_sup_span), and is proved via the Atkin–Lehner involution relation [`ModularForm.alSlash_alSlash`](thm.html#ModularForm.alSlash_alSlash) together with [`CuspForm.traceLin_rescaleLin`](thm.html#CuspForm.traceLin_rescaleLin).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_sum_range_slash_heckeDiagMatrix_heckeDiagMatrix_conj_eq.lean

import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped ModularForm MatrixGroups in

theorem CuspForm.sum_range_slash_heckeDiagMatrix_heckeDiagMatrix_conj_eq
    {N q : ℕ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hq : q.Prime) (hqN : ¬ q ∣ N) :
    ∑ j ∈ Finset.range q,
      ((⇑f ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q)
        ∣[(2 : ℤ)] (ModularGroup.S * ModularGroup.T ^ (-((q * N * j : ℕ) : ℤ)) * ModularGroup.S⁻¹)
      = (ModularForm.heckeT 2 q ⇑f) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q - ⇑f := by sorry
