-- Prove2me | Theorems.Thm_CubicProductLB_lemma_19
-- name    : CubicProductLB.lemma_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:21:38.228204+00:00
-- url     : https://prove2.me/theorems/95095c99-6c0a-4664-80ff-2b0d8c5968bf
-- title:
--   Lemma 19 — finite-counting triple clustering
-- statement:
--   Fix $r \ge 1$. There exist constants $\gamma_r > 1$ and $N_0(r)$ with the following property. Let $N = 3 \cdot 2^d \ge N_0(r)$ and suppose
--   $$G(z) = \sum_{q=1}^S f_q(z) \pmod 2,$$
--   where every $f_q$ has an $r$-observation representation over $\mathbb F_3$. If $S < \gamma_r^N$, then there is a triple partition $P$ of $[N]$ such that $G \circ \iota_P$ is 2-simple.
--
--   The constants depend on $r$ only. A sum of fewer than exponentially many bounded-observation functions can therefore be simplified by a single identification of triples of variables.
--
--   **Formalization Note** The length is written $3 \cdot 2^d$ directly, so the clustered length is $M = 2^d$ with no division.
--
--   Differences from the source:
--   - encoding: G a sum of f_1, …, f_S → a sum over Fin S, with G written as fun z => ∑ q, f q z; reason: same object
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Lemma 19, Eqs. (304)–(307), p.35

import Mathlib
import Definitions.Def_CubicProductLB_TriplePartition
import Definitions.Def_CubicProductLB_IsTwoSimple
import Definitions.Def_CubicProductLB_HasObsRep

namespace CubicProductLB

/-- Lemma 19 (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Lemma 19, Eqs. (304)–(307), p.35). Fix `r ≥ 1`. There are `γ_r > 1` and `N_0(r)` such
that for `N = 3 · 2^d ≥ N_0(r)`, if `G = ∑_{q ≤ S} f_q` over `F_2` with every `f_q` having an `r`-observation
representation over `F_3` and `S < γ_r^N`, then `G ∘ ι_P` is 2-simple for some triple partition `P` of `[N]`.

**Formalization Note** `γ` and `N₀` depend on `r` only. `N = 3 · 2^d` is written directly, so
`M = N/3 = 2^d` involves no division. -/
theorem lemma_19 (r : ℕ) (hr : 1 ≤ r) :
    ∃ γ : ℝ, 1 < γ ∧ ∃ N₀ : ℕ, ∀ d : ℕ, N₀ ≤ 3 * 2 ^ d →
      ∀ (S : ℕ) (f : Fin S → (Fin (3 * 2 ^ d) → Bool) → ZMod 2),
        (∀ q, HasObsRep r (f q)) → (S : ℝ) < γ ^ (3 * 2 ^ d) →
        ∃ P : TriplePartition (2 ^ d), IsTwoSimple ((fun z => ∑ q, f q z) ∘ P.iota) := by sorry

end CubicProductLB
