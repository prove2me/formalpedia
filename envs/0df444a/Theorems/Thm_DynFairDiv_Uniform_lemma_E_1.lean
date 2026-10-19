-- Prove2me | Theorems.Thm_DynFairDiv_Uniform_lemma_E_1
-- name    : DynFairDiv.Uniform.lemma_E_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:58.221843+00:00
-- url     : https://prove2.me/theorems/65129b61-9f6c-4b30-bc87-afc5ba797650
-- title:
--   Lemma E.1, p. 959 — closed form of FFA's allocations on the infinite d-uniform control vector
-- statement:
--   Fix $d \ge 1$ and $\sigma \in \mathbb{R}$, and run the frugally fair algorithm on the infinite $d$-uniform control vector ($\psi[t] = d$ for all $t$). Write $t = \ell(d+1) + i$ with integers $\ell \ge 0$ and $0 \le i \le d$, so that $t - \ell = \ell d + i$. Then the allocation when $t$ users are present is, in order,
--   $$X^t = \Big(\underbrace{\tfrac{\sigma}{t-\ell},\dots,\tfrac{\sigma}{t-\ell}}_{i\ \text{terms}},\ \underbrace{\tfrac{\sigma}{t-\ell+1},\dots,\tfrac{\sigma}{t-\ell+1}}_{d+1\ \text{terms}},\ \dots,\ \underbrace{\tfrac{\sigma}{t},\dots,\tfrac{\sigma}{t}}_{d+1\ \text{terms}}\Big),$$
--   that is, $i$ copies of $\sigma/(\ell d + i)$ followed, for $k = 1, \dots, \ell$, by $d+1$ copies of $\sigma/(\ell d + i + k)$.
--
--   This closed form gives the total $S^t$ explicitly and is the basis for computing the optimal fairness ratio of $d$-uniform control vectors.
--
--   **Formalization Note.** Stated as an equality of lists (order included); both sides are empty at $t = 0$. The standing assumption $d \ge 1$ of §5.1 is kept.
-- source:
--   Vardi, Psomas, Friedman, Dynamic Fair Resource Division, Math. Oper. Res. 47(2):945–968 (2022), p. 959, Lemma E.1 (Appendix E.2)

import Mathlib
import Definitions.Def_DynFairDiv_Uniform_Model

namespace DynFairDiv.Uniform

theorem lemma_E_1 (d : ℕ) (hd : 1 ≤ d) (σ : ℝ) (ℓ i : ℕ) (hi : i ≤ d) :
    ffa (uniformCV d) σ (ℓ * (d + 1) + i) =
      List.replicate i (σ / ((ℓ * d + i : ℕ) : ℝ)) ++
      (List.range ℓ).flatMap
        (fun k => List.replicate (d + 1) (σ / ((ℓ * d + i + k + 1 : ℕ) : ℝ))) := by sorry

end DynFairDiv.Uniform
