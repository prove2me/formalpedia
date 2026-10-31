-- Prove2me | Theorems.Thm_CoCoNet_superfair_shift_identity
-- name    : CoCoNet.superfair_shift_identity
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:42.930766+00:00
-- url     : https://prove2.me/theorems/2518141e-4400-4b12-9903-8ba98879cb09
-- title:
--   §3.3, p.19 — $\hat\Phi(s)=\Phi(s)-(I-W)d_{H(\Phi(s))}$
-- statement:
--   Let $(m,W)$ be admissible, $l\ge0$, and let $\Phi$ be the fair map (credit amounts $c_j=m_jl_j$). Let $d\in\mathbb R^n_+$ and let $\hat\Phi$ be the map of the super-fair case with the same $m$, $W$, $l$ and smaller credit amounts $\hat c_j=c_j-d_j$. Then for every $s\in\mathbb R^n$
--   $$\hat\Phi(s)=\Phi(s)-(I-W)\,d_{H(\Phi(s))},$$
--   where $H(a)$ is the set of banks healthy at $a$ in the fair case.
--
--   The super-fair map is thus the fair map shifted, at each point, by the vectors $d_j(I-W)e_j$ of the healthy banks; the existence proof for the super-fair case works with these shifts.
--
--   Differences from the source:
--   - reading: no sign condition on the thresholds l stated → 0 ≤ l; reason: the paper asserts that the sets S_{B,C,H} partition ℝⁿ (p.12), which holds iff l ≥ 0; in the paper's setting lᵢ ≥ cᵢ/mᵢ with nonnegative debts cᵢ; without it the sets read off s overlap and Φ is not continuous
--   - generalization: §3.3 assumes I − W invertible 'throughout this section' (p.18) → no IsUnit (1 - W) hypothesis; reason: the identity only needs the fair map to be injective (Proposition 4), which holds without Assumption 1; the instances with I − W invertible are the section's claim
--   - encoding: fair credit amounts c with lᵢ = cᵢ/mᵢ → credit vector m * l (pointwise); reason: since mᵢ > 0, lᵢ = cᵢ/mᵢ is equivalent to cᵢ = mᵢlᵢ
--   - encoding: H(a) = {i : Φ⁻¹(a)ᵢ > ℓᵢ} with Φ the fair bijection → Hfair m W l a, built with Function.invFun of the fair map; reason: the fair map is a bijection under the stated hypotheses (Proposition 4), so invFun is its inverse
--   - encoding: banks [n] = {1, …, n}; vectors in ℝⁿ; matrix W = (w_ij) → banks Fin n (0-based); vectors Fin n → ℝ; W : Matrix (Fin n) (Fin n) ℝ with W i j = w_ij; reason: same objects, relabelled from 0
-- source:
--   Balter, Schweizer & Vera, Contingent Capital with Stock Price Triggers in Interbank Networks, arXiv:2011.06474v1, §3.3, p.19, display 'Φ̂(s) = Φ(s) − (I − W)d_{H(Φ(s))}'

import Mathlib
import Definitions.Def_CoCoNet_IsAdmissible
import Definitions.Def_CoCoNet_restrictTo
import Definitions.Def_CoCoNet_Phi
import Definitions.Def_CoCoNet_Hfair
open Matrix

namespace CoCoNet

/-- **The super-fair map is the fair map shifted by the healthy banks' credit reductions.**
Balter, Schweizer & Vera, arXiv:2011.06474v1, §3.3, p.19: "Now we introduce the super-fair case Φ̂
which has the same values of m, W and l but smaller credit amounts, ĉⱼ = cⱼ − dⱼ, dⱼ ≥ 0 for all
j ∈ [n]. … For s ∈ S_{B,C,H}, we know that Φ̂(s) = L_{B,C}s + (I − W)ĉ_H which implies that the two
mappings Φ and Φ̂ are related via Φ̂(s) = Φ(s) − (I − W)d_{H(Φ(s))} for all s."

Here `Φ = Phi m W l (m * l)` is the fair map, `Φ̂ = Phi m W l (m * l - d)` and `H = Hfair`.

**Formalization Note.** The fair credit `c` with `lᵢ = cᵢ/mᵢ` is written `m * l`. `0 ≤ l` is a
reading (as in Proposition 3). Stated without Assumption 1 (a generalization of §3.3's standing
assumption, p.18): the identity only needs the fair map to be injective (Proposition 4). -/
theorem superfair_shift_identity {n : ℕ} (m : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℝ)
    (l d : Fin n → ℝ) (hadm : IsAdmissible m W) (hl : 0 ≤ l) (hd : 0 ≤ d) (s : Fin n → ℝ) :
    Phi m W l (m * l - d) s =
      Phi m W l (m * l) s - (1 - W) *ᵥ restrictTo (Hfair m W l (Phi m W l (m * l) s)) d := by sorry

end CoCoNet
