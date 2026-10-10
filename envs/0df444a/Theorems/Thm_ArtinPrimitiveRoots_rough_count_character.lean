-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_rough_count_character
-- name    : ArtinPrimitiveRoots.rough_count_character
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T12:52:56.705977+00:00
-- url     : https://prove2.me/theorems/d719543e-123b-435d-8a17-64a2626060c1
-- title:
--   (10.17), proof of Proposition 10.3 (OpenAI) — the W-rough integers of a dyad, twisted by a character, are counted by V(W)|I′|
-- statement:
--   Fix $0 < w_- < w_+ < 1$, and write $L = \log x$, $W = \exp(L^{0.24})$ (`sieveLevel x`) and $V(W) = \prod_{p \le W}(1 - 1/p)$ (`mertensProduct`). For all $A_0, A_1 > 0$ there are $K$ and $x_0$ such that for every $x \ge x_0$, every $M > 0$ with $w_- \le \log M/L$ and $\log(2M)/L \le w_+$, every Dirichlet character $\chi$ modulo $k$ with $1 \le k \le L^{A_0}$, and every interval $I' \subseteq [M, 2M]$,
--
--   $$\Bigl|\sum_{\substack{m \in I'\\ P^-(m) > W}} \chi(m) - \mathbf 1_{\chi\ \mathrm{principal}}\,V(W)\,|I'|\Bigr| \le K M L^{-A_1},$$
--
--   where $|I'|$ is the length of $I'$ and $P^-(m) > W$ means that every prime factor of $m$ exceeds $W$ (`IsRough`). $K$ and $x_0$ depend on $w_\pm, A_0, A_1$.
--
--   This is the small-prime count in the paper's proof of Proposition 10.3, which the paper cites as Lemma 2.5 of OpenAI's *The Poisson–Dirichlet law for prime predecessors*. Published as a step of that proof.
--
--   **Formalization note.** The setting is that of Proposition 10.3 with $M = H_m$, as in (10.15): $[\log H_m/L, \log(2H_m)/L] \subseteq [w_-, w_+]$ (p. 67), and $M > 0$. The principal character is $\chi = 1$ in Mathlib's `DirichletCharacter ℂ k`; characters are zero on nonunits. "Every interval" is any order-connected set $I' \subseteq [M, 2M]$, and its length is its Lebesgue measure; "$k \le L^{A_0}$" is read as $1 \le k \le L^{A_0}$.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 68: “The matching small-prime count is $\sum_{m \in I',\ P^-(m) > W}\chi(m) = \mathbf 1_{\chi\ \text{principal}}V(W)|I'| + O(ML^{-A_1})$ (10.17) for every fixed $A_1$, with the same interval and character uniformity. This is [21, Lemma 2.5]. Notice that all prime divisors of $k \le L^{A_0}$ are less than $W$ for large $x$, so its principal character is one on the rough support.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 68, proof of Proposition 10.3, (10.17)

import Mathlib
import Definitions.Def_ArtinSieve

namespace ArtinPrimitiveRoots

open Real

open Classical in
theorem rough_count_character (wMinus wPlus : ℝ) (hw : 0 < wMinus) (hww : wMinus < wPlus)
    (hwPlus : wPlus < 1) :
    ∀ A₀ A₁ : ℝ, 0 < A₀ → 0 < A₁ →
      ∃ K x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ M : ℝ, 0 < M → wMinus ≤ log M / log x → log (2 * M) / log x ≤ wPlus →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ log x ^ A₀ → ∀ χ : DirichletCharacter ℂ k,
      ∀ J : Set ℝ, J.OrdConnected → J ⊆ Set.Icc M (2 * M) →
        ‖(∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1),
            if (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m then χ (m : ZMod k) else 0) -
          (if χ = 1 then
            ((mertensProduct (sieveLevel x) * (MeasureTheory.volume J).toReal : ℝ) : ℂ)
          else 0)‖ ≤ K * (M * log x ^ (-A₁)) := by
  sorry

end ArtinPrimitiveRoots
