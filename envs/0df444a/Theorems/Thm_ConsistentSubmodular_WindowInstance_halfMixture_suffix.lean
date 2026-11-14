-- Prove2me | Theorems.Thm_ConsistentSubmodular_WindowInstance_halfMixture_suffix
-- name    : ConsistentSubmodular.WindowInstance.halfMixture_suffix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:43.965766+00:00
-- url     : https://prove2.me/theorems/eff9f7e4-a526-4866-be8b-6f1dbbe678a2
-- title:
--   Theorem B.4 (suffix part) — persistence of the half mixture after $c$
-- statement:
--   Let $W$ be a window instance with stages $0,\dots,m$, and write $\lambda_j=f(R_j)$, $r_{i,j}=f(R_j\cup O_i)-\lambda_j$, $P_j=f(O_j\cup R_j)$, $K_j=2(P_j-\lambda_j)-r_{0,j}$ and $D_\beta=\max_i\bigl(2K_i-4(1-\beta)P_i\bigr)$. Let $\tfrac12\le\beta\le\tfrac34$ and let $\alpha$ be real with $2\beta\alpha\le 1$. Let $c$ be a stage such that $K_j<D_\beta$ for all $j>c$. Then for every stage $j>c$,
--   $$\alpha\,P_j\;\le\;\lambda_j+\frac{r_{0,j}+r_{c,j}+\max(r_{0,j},r_{c,j})}{4}.$$
--
--   For $j>c$ the failure of eligibility together with the benchmark credit (31) of the partner gives the premise (32) of Lemma B.6, so the reserve $L_j$ of (33) dominates $\alpha P_j$. The right-hand side is a lower bound for the value of the half mixture at stage $j$, which makes the anchor persistent on the suffix in Theorem B.4.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/HalfMixtureCertificate.lean#L232-L276 (`ConsistentSubmodular.WindowInstance.halfMixture_suffix`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_HalfMixtureCertificate

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.WindowInstance
variable {n : ℕ} (W : WindowInstance n)

theorem ConsistentSubmodular.WindowInstance.halfMixture_suffix {α β : ℝ} (hβ : 1 / 2 ≤ β) (hβ' : β ≤ 3 / 4)
    (hα : 2 * β * α ≤ 1) {c : Fin (W.lastStage + 1)}
    (hafter : ∀ j, c < j → W.credit j < W.envelope β)
    {j : Fin (W.lastStage + 1)} (hcj : c < j) :
    α * W.benchmark j ≤ W.arrivalValue j +
      (W.residual 0 j + W.residual c j + max (W.residual 0 j) (W.residual c j)) / 4 := by sorry
