-- Prove2me | Theorems.Thm_ChoresEFX_Supplement_theorem_C_1
-- name    : ChoresEFX.Supplement.theorem_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:03:24.492323+00:00
-- url     : https://prove2.me/theorems/b08421da-a539-4e66-8b74-a7b3c4c889aa
-- title:
--   Theorem C.1 — the MFCP → SSR pipeline has EFkX ratio at least $2+1/k-6/r$ on some instance
-- statement:
--   Fix an integer $k\ge1$ and an integer $r\ge3$, and set
--   $$t=\frac{1}{100\,r\,(k+1)},\qquad \beta=\frac{1+2t}{k+1}.$$
--   There is an instance $I_{k,r}$ — a number $n\ge1$ of agents, a number $m$ of chores and a strictly positive rational cost matrix $(c_i(g))$ — with the following properties.
--
--   1. **MFCP terminates in its first round.** At the initial weights $v\equiv1$ a water level $s$ exists, and at every water level a maximum flow of the network (3) exists and every maximum flow has value $n$. Hence no failed round of MFCP is possible.
--   2. **The pipeline has an output.** Some MFCP output $(p,\gamma,w)$, some sort order and some admissible matching exist.
--   3. **Every SSR output is bad.** For every MFCP output $(p,\gamma,w)$ (every legal maximum-flow choice), every sort order (every slot tie-break) and every admissible matching (every matching choice), the rounded allocation $Y$ satisfies
--   $$\operatorname{rat}_k(Y)\;\ge\;2+\frac1k-\frac6r,$$
--   where $\operatorname{rat}_k(Y)=\inf\{\alpha\ge1: Y\text{ is }\alpha\text{-EFkX}\}$.
--   4. **Envy repair does not help.** The same bound holds for every output of the whole pipeline (MFCP, SSR, packet decomposition, and the envy-repair stage APR with any repair factor $\lambda$).
--
--   Since the bound tends to $2+1/k$ as $r\to\infty$, the leading factor $2+1/k$ of the paper's analysis is asymptotically tight for this pipeline (for EFX, $k=1$, the factor $3$).
--
--   **Formalization Note** The pipeline is the published one: `IsMfcpOutput`, `IsSortedOrder`, `IsAdmissibleMatching` and `ssrBundle`, and `GeneralRun` for the full pipeline; the costs are the instance's rationals cast to the reals. $\operatorname{rat}_k(Y)\ge x$ is stated as "every $\alpha\ge1$ with $Y$ $\alpha$-EFkX satisfies $x\le\alpha$", not through a real infimum. Since the instance is positive, Algorithm 1's working costs are the input costs.
--
--   Differences from the source:
--   - reading: MFCP terminates in its first round → at v ≡ 1 a water level exists, and at every water level a maximum flow exists and every maximum flow has value n; reason: this is exactly "the first maximum flow has value n" for every legal flow choice, which rules out any failed round
--   - reading: every output Y of legal maximum-flow, slot-tie-breaking, and perfect-matching choices → an added conjunct that at least one such output exists, and the bound for every one; reason: the pipeline is an algorithm and has an output (Theorem 3.4 gives the matching); the conjunct keeps the universal clause from holding vacuously
--   - generalization: the specified pipeline (proof, p.22: "the envy-repair stage leaves the allocation unchanged") → the bound also for every GeneralRun output, with any APR factor λ; reason: on this instance no packets are formed, so APR returns the SSR allocation for every λ; it specializes to the pipeline's own λ
--   - encoding: rat_k(Y) ≥ 2 + 1/k − 6/r → ∀ α ≥ 1, Y α-EFkX → 2 + 1/k − 6/r ≤ α; reason: rat_k is an infimum over α ≥ 1, and inf S ≥ x iff every element of S is ≥ x (an empty S gives +∞ in the paper)
--   - encoding: perfect matching of the printed Algorithm 3 (with dummy chores) → the published dummy-free IsAdmissibleMatching; reason: the base mission's convention (paper.md decision 9); the outputs are the same allocations
-- source:
--   Qin, Fang, Li, Liu, Chen, Polynomial-Time Approximate EFX for Chores via Flow and Matching, STOC 2027 submission (manuscript sha256 b26d14cfae7201df0c48a376f019e1b4904b83856c5f916ac5f3c418207f4a89), Theorem C.1, p.21 (pdf p.21); proof pp.21–23, Table 2 p.22, display (16) p.23

import Mathlib
import Definitions.Def_ChoresEFX_Alg1Run

namespace ChoresEFX.Supplement

open ChoresEFX Finset

/-- **Theorem C.1 (Tightness of the fixed pipeline)**, p.21 (proof pp.21–23).

Qin, Fang, Li, Liu, Chen, *Polynomial-Time Approximate EFX for Chores via Flow and Matching*, STOC 2027
submission (manuscript sha256 b26d14cf…): "For every k ≥ 1 and integer r ≥ 3, set t = 1/[100r(k+1)].
There exists a positive rational instance I_{k,r} on which MFCP terminates in its first round and every
output Y of legal maximum-flow, slot-tie-breaking, and perfect-matching choices satisfies
rat_k(Y) ≥ 2 + 1/k − 6/r."

With `t = 1/(100 r (k+1))`, `β = (1+2t)/(k+1)` (`betaParam k t`) and `x = 2 + 1/k − 6/r`, there is a
well-formed rational instance with strictly positive costs such that
1. (MFCP terminates in its first round) at the initial weights `v ≡ 1` a water level exists, and at
   every water level a maximum flow exists and every maximum flow has value `n`; so no failed round
   is possible;
2. the pipeline MFCP → SSR has an output (some MFCP output, sort order and admissible matching);
3. for every MFCP output `(p, γ, w)` (every legal maximum-flow choice), every sort order `o` (every
   slot tie-break) and every admissible matching `π` (every matching choice), the rounded allocation
   `Y = ssrBundle π` has `rat_k(Y) ≥ x`, i.e. every `α ≥ 1` for which `Y` is `α`-EFkX is `≥ x`;
4. the same bound holds for every output of the whole pipeline `GeneralRun` (MFCP, SSR, packet
   decomposition and the envy-repair stage APR, with any repair factor `λ`): the proof shows on
   pp.22 that the envy-repair stage leaves the allocation unchanged.

**Formalization Note.** `rat_k(Y) = inf{α ≥ 1 : Y is α-EFkX}` (§2, p.5) is not defined as a real
`sInf`; `rat_k(Y) ≥ x` is stated as "every `α ≥ 1` with `Y` α-EFkX satisfies `x ≤ α`". The instance is
positive, so Algorithm 1's working costs equal the input costs (proof of Theorem 1.1, p.19) and the
pipeline runs on `I.realCost`. Every choice of every stage is universally quantified (paper.md
decision 8); SSR is in the published dummy-free form `IsAdmissibleMatching` (decision 9). -/
theorem theorem_C_1 (k : ℕ) (hk : 1 ≤ k) (r : ℕ) (hr : 3 ≤ r) :
    ∃ I : Inst, I.WellFormed ∧ (∀ i g, 0 < I.c i g) ∧
      let t : ℝ := 1 / (100 * (r : ℝ) * ((k : ℝ) + 1))
      let β : ℝ := betaParam k t
      let x : ℝ := 2 + 1 / (k : ℝ) - 6 / (r : ℝ)
      ((∃ s, IsWaterLevel I.realCost β (fun _ => (1 : ℝ)) s) ∧
        ∀ s, IsWaterLevel I.realCost β (fun _ => (1 : ℝ)) s →
          (∃ f, IsMaximumFlow I.realCost t β (fun _ => (1 : ℝ)) s f) ∧
          ∀ f, IsMaximumFlow I.realCost t β (fun _ => (1 : ℝ)) s f → flowValue f = (I.n : ℝ)) ∧
      (∃ (p : Fin I.m → ℝ) (γ : Fin I.n → ℝ) (w : Fin I.n → Fin I.m → ℝ) (o : Fin I.n → Fin I.m → ℕ)
          (π : Fin I.m → Σ i, Fin (numSlots w i)),
          IsMfcpOutput I.realCost t β p γ w ∧ IsSortedOrder β p o ∧ IsAdmissibleMatching w o π) ∧
      (∀ (p : Fin I.m → ℝ) (γ : Fin I.n → ℝ) (w : Fin I.n → Fin I.m → ℝ),
          IsMfcpOutput I.realCost t β p γ w →
          ∀ o : Fin I.n → Fin I.m → ℕ, IsSortedOrder β p o →
          ∀ π : Fin I.m → Σ i, Fin (numSlots w i), IsAdmissibleMatching w o π →
          ∀ α : ℝ, 1 ≤ α → IsAlphaEFkX I.realCost k α (ssrBundle π) → x ≤ α) ∧
      (∀ (lam : ℝ) (X : Fin I.n → Finset (Fin I.m)), GeneralRun I.realCost k t lam X →
          ∀ α : ℝ, 1 ≤ α → IsAlphaEFkX I.realCost k α X → x ≤ α) := by sorry

end ChoresEFX.Supplement
