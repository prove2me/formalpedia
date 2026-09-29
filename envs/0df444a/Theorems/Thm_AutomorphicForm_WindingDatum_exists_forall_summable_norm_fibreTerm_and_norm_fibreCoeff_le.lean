-- Prove2me | Theorems.Thm_AutomorphicForm_WindingDatum_exists_forall_summable_norm_fibreTerm_and_norm_fibreCoeff_le
-- name    : AutomorphicForm.WindingDatum.exists_forall_summable_norm_fibreTerm_and_norm_fibreCoeff_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/2d037d58-edde-5959-b475-cca6f1f86f95
-- title:
--   Uniform absolute bound for fibre coefficients of a winding datum
-- statement:
--   Let $r,d,c$ be natural numbers and let $\mathcal D$ be a winding datum of signature $(r,d,c)$, i.e. a term of [`AutomorphicForm.WindingDatum r d c`](def/AutomorphicForm_WindingDatum.html#L11): a subgroup $\Lambda$ of $(\mathrm{Fin}\,r\to\mathbb R)\times(\mathrm{Fin}\,d\to\mathbb Z)$ carrying the discrete topology, an $\mathbb R$-linear functional $s$ on $\mathbb R^r$ and a nonzero $\omega\colon \mathrm{Fin}\,d\to\mathbb R$ with $s(x_1)=\sum_i \omega_i\,x_{2,i}$ for all $x\in\Lambda$, a homomorphism $\chi\colon\Lambda\to(\mathbb R/\mathbb Z)^c$, subgroups $\mathcal D.\mathrm{sub}\,i\le\Lambda$ indexed by $i\in\mathbb N$, continuous integrable windows $\Psi_i\colon\mathbb R^r\to\mathbb C$ with $\|\Psi_i(x)\|\le C_i\prod_k(1+|x_k|)^{-2}$ and the same majorant for the Fourier transform $\xi\mapsto\int e(-\langle\xi,x\rangle)\Psi_i(x)\,dx$, twist exponents $m_i\colon\mathrm{Fin}\,c\to\mathbb Z$, phases $\theta_{0,i}$, real shifts $x_{0,i}$, together with the remaining fields of the structure, which supply the integral shifts $n_{0,i}$, the weights $\mathcal D.\mathrm{lam}\,i$ and the conditions imposed on them. Then there is a constant $K\ge 0$, independent of the index $i$ and of $n$, such that for every $i\in\mathbb N$ and every $n\colon\mathrm{Fin}\,d\to\mathbb Z$ the family of norms of the fibre terms $$\mathcal D.\mathrm{fibreTerm}\,i\,n\,\gamma=\begin{cases}\Psi_i(x_{0,i}+\gamma_1)\prod_j \mathrm{fourier}(m_{i,j})\bigl(\theta_{0,i,j}+\chi(\gamma)_j\bigr),&\gamma_2+n_{0,i}=n,\\0,&\text{otherwise},\end{cases}$$ is summable over $\gamma\in\mathcal D.\mathrm{sub}\,i$, with $\sum'_{\gamma}\|\mathcal D.\mathrm{fibreTerm}\,i\,n\,\gamma\|\le K\,C_i$, and the fibre coefficient $\mathcal D.\mathrm{fibreCoeff}\,i\,n=\sum'_{\gamma}\mathcal D.\mathrm{fibreTerm}\,i\,n\,\gamma$ satisfies $\|\mathcal D.\mathrm{fibreCoeff}\,i\,n\|\le K\,C_i$; moreover, for every $n$ the family $i\mapsto\|\mathcal D.\mathrm{lam}\,i\cdot\mathcal D.\mathrm{fibreCoeff}\,i\,n\|$ is summable.
--
--   This is the absolute-convergence statement for the series defining the coefficient array of a winding datum, together with the uniform majorant $K\,C_i$ for the total mass of the $i$-th fibre, which is what permits countably many windows to be superposed. It is used in the identifications of the coefficients of a winding datum as double sums and in the evaluation of orbital integrals attached to such data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_WindingDatum_exists_forall_summable_norm_fibreTerm_and_norm_fibreCoeff_le.lean

import Mathlib
import Definitions.Def_AutomorphicForm_WindingDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AutomorphicForm.WindingDatum.exists_forall_summable_norm_fibreTerm_and_norm_fibreCoeff_le
    {r d c : ℕ} (𝒟 : AutomorphicForm.WindingDatum r d c) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ (i : ℕ) (n : Fin d → ℤ),
        Summable (fun γ : 𝒟.sub i => ‖𝒟.fibreTerm i n γ‖) ∧
        ∑' γ : 𝒟.sub i, ‖𝒟.fibreTerm i n γ‖ ≤ K * 𝒟.C i ∧
        ‖𝒟.fibreCoeff i n‖ ≤ K * 𝒟.C i) ∧
      ∀ n : Fin d → ℤ, Summable fun i : ℕ => ‖𝒟.lam i * 𝒟.fibreCoeff i n‖ := by sorry
