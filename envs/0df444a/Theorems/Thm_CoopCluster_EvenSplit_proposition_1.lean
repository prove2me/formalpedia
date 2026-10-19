-- Prove2me | Theorems.Thm_CoopCluster_EvenSplit_proposition_1
-- name    : CoopCluster.EvenSplit.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:06.159499+00:00
-- url     : https://prove2.me/theorems/afa3df6c-767e-4d03-b157-b5e16a79112d
-- title:
--   Proposition 1, p. 110 (PDF 5) — the monopoly optimum: αM is the unique root of (2) and pM = (B − hwe^{−δαM} + β0γ)/(2β0)
-- statement:
--   Consider the local monopolist of §2 under the standing assumptions, with profit $\Pi(p,\alpha)=p\,\lambda(p,\alpha;w)-\tfrac12c\alpha^2-\gamma(\lambda(p,\alpha;w)+1/w)$, $\lambda(p,\alpha;w)=B-hw e^{-\delta\alpha}-\beta_0p$, maximized over $p\ge\gamma$ and $\alpha\ge0$.
--
--   1. There is $\alpha^M\ge 0$ solving
--   $$\delta hw\bigl(B-hw e^{-\delta\alpha}-\beta_0\gamma\bigr)-2\beta_0c\,\alpha e^{\delta\alpha}=0 \tag{2}$$
--   at $\alpha=\alpha^M$.
--   2. $\alpha^M$ is the only solution of (2) on $\alpha\ge 0$.
--   3. A pair $(p,\alpha)$ is a monopoly optimum if and only if $\alpha=\alpha^M$ and
--   $$p=p^M=\frac{B-hw e^{-\delta\alpha^M}+\beta_0\gamma}{2\beta_0}.$$
--
--   In particular the monopoly optimum exists and is unique; this is the benchmark against which co-opetition is compared in Proposition 7.
--
--   **Formalization Note.** The standing assumptions use the strict capacity bound $\beta_0\gamma<B-hw$ (see the model file).
-- source:
--   Yuan, Dai, Chen & Gavirneni, Co-opetition in service clusters with waiting-area entertainment, MSOM 23(1):106–122 (2021), p. 110 (PDF 5), Proposition 1, eq. (2)

import Mathlib
import Definitions.Def_CoopCluster_EvenSplit_Model

namespace CoopCluster.EvenSplit

theorem proposition_1 (M : Params) (hS : M.Standing) :
    ∃ αM : ℝ, 0 ≤ αM ∧
      M.δ * M.h * M.w * (M.B - M.h * M.w * Real.exp (-(M.δ * αM)) - M.b0 * M.γ)
          - 2 * M.b0 * M.c * αM * Real.exp (M.δ * αM) = 0 ∧
      (∀ α : ℝ, 0 ≤ α →
        M.δ * M.h * M.w * (M.B - M.h * M.w * Real.exp (-(M.δ * α)) - M.b0 * M.γ)
            - 2 * M.b0 * M.c * α * Real.exp (M.δ * α) = 0 → α = αM) ∧
      (∀ p α : ℝ, IsMonoOpt M p α ↔
        (α = αM ∧
          p = (M.B - M.h * M.w * Real.exp (-(M.δ * αM)) + M.b0 * M.γ) / (2 * M.b0))) := by sorry

end CoopCluster.EvenSplit
