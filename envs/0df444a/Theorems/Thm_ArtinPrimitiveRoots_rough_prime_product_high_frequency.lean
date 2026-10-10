-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_rough_prime_product_high_frequency
-- name    : ArtinPrimitiveRoots.rough_prime_product_high_frequency
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T12:52:48.569265+00:00
-- url     : https://prove2.me/theorems/50c42307-1d70-42c3-bca3-80ade59df7b8
-- title:
--   Proof of Proposition 10.3, after (10.18) (OpenAI) — at frequencies L^{B₀} ≤ |u| ≤ x², M⁻¹ Σ_{m∈I} R_γ(m) χ(m) m^{iu} ≪ L^{−A}
-- statement:
--   Fix $0 < \gamma < w_- < w_+ < 1$, and write $L = \log x$ and $R_\gamma(m) = \mathbf 1_{P^-(m) > x^\gamma}$ (`IsRough (x ^ γ) m`). For all $A_0, A > 0$ there are $B_0$, $K$ and $x_0$ such that for every $x \ge x_0$, every $M > 0$ with $w_- \le \log M/L$ and $\log(2M)/L \le w_+$, every Dirichlet character $\chi$ modulo $k$ with $1 \le k \le L^{A_0}$, every interval $I \subseteq [M, 2M]$, and every real $u$ with $L^{B_0} \le |u| \le x^2$,
--
--   $$\Bigl|\frac1M\sum_{m \in I} R_\gamma(m)\chi(m)\,m^{iu}\Bigr| \le K L^{-A}.$$
--
--   $B_0$, $K$ and $x_0$ depend on $\gamma, w_\pm, A_0, A$.
--
--   This is the high-frequency bound for the prime-product part of the coefficient (10.13), in the paper's proof of Proposition 10.3. The paper derives it from the long prime polynomial estimate (10.18) of its companion paper, published here as `long_prime_polynomial`. Published as a step of that proof.
--
--   **Formalization note.** The setting is that of Proposition 10.3 with $M = H_m$ (p. 67), and $M > 0$. The paper's $B_0 = B_0(\tau_{lp}, \theta_{lp}, A_0, A_3)$ comes from (10.18) with fixed $0 < \tau_{lp} < \gamma$ and $w_+ < \theta_{lp} < 1$ and $A_3$ chosen for the requested saving $A$, so here it is chosen after $A_0$ and $A$. Characters are Mathlib's `DirichletCharacter ℂ k`, zero on nonunits; "an interval" is any order-connected set $I \subseteq [M, 2M]$; "$k \le L^{A_0}$" is read as $1 \le k \le L^{A_0}$.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 69: “For fixed $0 < \tau_{lp} < \theta_{lp} < 1$ and fixed $A_0, A_3 > 0$, the prime estimate gives a constant $B_0 = B_0(\tau_{lp}, \theta_{lp}, A_0, A_3)$ such that $\Bigl|\sum_{p \in J'}\chi(p)p^{-1+iu}\Bigr| \ll L^{-A_3}$ (10.18) for every interval $J' \subseteq [P, 2P]$, every character modulo $k \le L^{A_0}$, and $x^{\tau_{lp}}/2 \le P \le x^{\theta_{lp}}$, $L^{B_0} \le |u| \le x^2$. Choose $0 < \tau_{lp} < \gamma$ and $w_+ < \theta_{lp} < 1$. […] Taking $A_3$ to absorb the $O(L^j)$ boxes and using Equation (10.14) proves any requested logarithmic saving for $M^{-1}\sum_{m \in I}R_\gamma(m)\chi(m)m^{iu}$ throughout this range.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 69, proof of Proposition 10.3, the prime-convolution bound after (10.18)

import Mathlib
import Definitions.Def_ArtinSieve

namespace ArtinPrimitiveRoots

open Real

open Classical in
theorem rough_prime_product_high_frequency (γ wMinus wPlus : ℝ) (hγ : 0 < γ)
    (hγw : γ < wMinus) (hww : wMinus < wPlus) (hwPlus : wPlus < 1) :
    ∀ A₀ A : ℝ, 0 < A₀ → 0 < A →
      ∃ B₀ K x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ M : ℝ, 0 < M → wMinus ≤ log M / log x → log (2 * M) / log x ≤ wPlus →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ log x ^ A₀ → ∀ χ : DirichletCharacter ℂ k,
      ∀ J : Set ℝ, J.OrdConnected → J ⊆ Set.Icc M (2 * M) →
      ∀ u : ℝ, log x ^ B₀ ≤ |u| → |u| ≤ x ^ 2 →
        ‖((1 / M : ℝ) : ℂ) * ∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1),
            (if (m : ℝ) ∈ J ∧ IsRough (x ^ γ) m then
              χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * u) else 0)‖ ≤ K * log x ^ (-A) := by
  sorry

end ArtinPrimitiveRoots
