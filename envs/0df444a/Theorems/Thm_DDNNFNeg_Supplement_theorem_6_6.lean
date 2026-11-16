-- Prove2me | Theorems.Thm_DDNNFNeg_Supplement_theorem_6_6
-- name    : DDNNFNeg.Supplement.theorem_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:51:59.063193+00:00
-- url     : https://prove2.me/theorems/e9b081a4-8235-4bd4-acdf-b13611750e0d
-- title:
--   Theorem 6.6 — $F_k$ on $N=\Theta(k^2)$ variables with a structured d-DNNF of size $2^{O(k)}$ while every DNNF for $\neg F_k$ has size $2^{\Omega(k^2)}$
-- statement:
--   There are constants $c_1, C_1, C_2, c > 0$ such that for every sufficiently large integer $k$ there are $N$ with
--
--   $$c_1 k^2 \le N \le C_1 k^2$$
--
--   and a Boolean function $F_k : \{0,1\}^N \to \{0,1\}$ such that
--
--   1. $F_k$ is computed by a structured d-DNNF with at most $2^{C_2 k}$ gates, and
--   2. every DNNF computing $\neg F_k$ has at least $2^{c k^2}$ gates.
--
--   This is the unpadded form of Theorem 1.2, which follows from it by adding dummy variables; it is also the source of the UFA/CFG separation of Theorem 1.4.
--
--   **Formalization Note** All four constants are fixed before the threshold for $k$. The structured d-DNNF has literal input gates, is decomposable and deterministic, and respects one vtree over the $N$ variables.
--
--   Differences from the source:
--   - reading: for every sufficiently large k; N = Θ(k²); size 2^{O(k)}; size 2^{Ω(k²)} → constants c₁, C₁, C₂, c > 0 fixed first, then ∃ k₀ ∀ k ≥ k₀ with c₁k² ≤ N ≤ C₁k², size ≤ 2^{C₂k}, size ≥ 2^{ck²}; reason: standard reading of asymptotic notation, the same as in the published goal
--   - reading: structured d-DNNF (described informally, defined in [AAC+24]) → constant-free d-DNNF respecting one vtree over the variables (Pipatsrisawat–Darwiche definition); reason: the paper defers the definition to the cited literature; this is its standard form
--   - generalization: every DNNF computing ¬f (NNFs have literal input gates) → every DNNF computing ¬f, constant leaves also allowed; reason: a larger class of circuits; it contains the paper's DNNFs, so the bound specializes to the source; it also prevents the trivialization by f ≡ 1, since no constant-free DNNF computes the constant 0
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Theorem 6.6, p.18

import Mathlib
import Definitions.Def_DDNNFNeg_NNF_Computes
import Definitions.Def_DDNNFNeg_NNF_IsConstFree
import Definitions.Def_DDNNFNeg_NNF_IsDDNNF
import Definitions.Def_DDNNFNeg_Supplement_IsStructured

namespace DDNNFNeg.Supplement

/-- **Theorem 6.6** (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), p.18): for every sufficiently large integer `k`, there is a Boolean
function `F_k : {0,1}^N → {0,1}`, where `N = Θ(k²)`, such that `F_k` is computable by a
structured d-DNNF of size `2^{O(k)}`, but every DNNF computing `¬F_k` has size `2^{Ω(k²)}`.

**Formalization Note** The constants `c₁, C₁` of `N = Θ(k²)` (two-sided), `C₂` of `2^{O(k)}` and
`c` of `2^{Ω(k²)}` are positive and fixed before the threshold `k₀` and `k`. The structured
d-DNNF is constant-free, decomposable, deterministic and respects one vtree over the `N`
variables. The lower bound quantifies over every DNNF, with constant leaves also allowed, as in
the published goal `DDNNFNeg.theorem_1_1`. -/
theorem theorem_6_6 :
    ∃ c₁ C₁ C₂ c : ℝ, 0 < c₁ ∧ 0 < C₁ ∧ 0 < C₂ ∧ 0 < c ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ N : ℕ,
      c₁ * (k : ℝ) ^ 2 ≤ N ∧ (N : ℝ) ≤ C₁ * (k : ℝ) ^ 2 ∧ ∃ F : (Fin N → Bool) → Bool,
        (∃ D : NNF (Fin N), D.IsConstFree ∧ D.IsDDNNF ∧ IsStructured D ∧ D.Computes F ∧
          (D.size : ℝ) ≤ (2 : ℝ) ^ (C₂ * k)) ∧
        (∀ D : NNF (Fin N), D.IsDNNF → D.Computes (fun x => !F x) →
          (2 : ℝ) ^ (c * (k : ℝ) ^ 2) ≤ (D.size : ℝ)) := by sorry

end DDNNFNeg.Supplement
