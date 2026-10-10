-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_rough_prime_product_count
-- name    : ArtinPrimitiveRoots.rough_prime_product_count
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T12:52:54.591978+00:00
-- url     : https://prove2.me/theorems/5028be6f-2066-48ba-90e1-a651bd52c6e8
-- title:
--   (10.15), proof of Proposition 10.3 (OpenAI) — the x^γ-rough integers of a dyad, twisted by a character, are counted by (1/L)∫ D_γ(log y/L) dy
-- statement:
--   Fix $0 < \gamma < w_- < w_+ < 1$, and write $L = \log x$ and $R_\gamma(m) = \mathbf 1_{P^-(m) > x^\gamma}$ (`IsRough (x ^ γ) m`: every prime factor of $m$ exceeds $x^\gamma$). For all $A_0, A_1 > 0$ there are $K$ and $x_0$ such that for every $x \ge x_0$, every $M > 0$ with $w_- \le \log M/L$ and $\log(2M)/L \le w_+$, every Dirichlet character $\chi$ modulo $k$ with $1 \le k \le L^{A_0}$, and every interval $I' \subseteq [M, 2M]$,
--
--   $$\Bigl|\sum_{m \in I'} R_\gamma(m)\chi(m) - \mathbf 1_{\chi\ \mathrm{principal}}\,\frac1L\int_{I'} D_\gamma(\log y/L)\,dy\Bigr| \le K M L^{-A_1}.$$
--
--   Here $D_\gamma$ is the rough-number density of (10.11) (`roughDensity`). $K$ and $x_0$ depend on $\gamma, w_\pm, A_0, A_1$.
--
--   This is the low-frequency counting formula in the paper's proof of Proposition 10.3. The paper proves it from the Siegel–Walfisz theorem, through (10.12), (10.14) and (10.16). Published as a step of that proof.
--
--   **Formalization note.** The setting is that of Proposition 10.3 with $M = H_m$: $[\log H_m/L, \log(2H_m)/L] \subseteq [w_-, w_+]$ (p. 67), and $M > 0$ since it is the scale of a dyad. The principal character is $\chi = 1$ in Mathlib's `DirichletCharacter ℂ k`; characters are zero on nonunits. "Every interval $I' \subseteq [M, 2M]$" is any order-connected set $I' \subseteq [M, 2M]$, and "$k \le L^{A_0}$" is read as $1 \le k \le L^{A_0}$.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 68: “We next obtain the counting formula needed at low frequencies. For every fixed $A_1, A_0 > 0$, every $k \le L^{A_0}$, every character $\chi$ mod $k$, and every interval $I' \subseteq [M, 2M]$, we claim $\sum_{m \in I'} R_\gamma(m)\chi(m) = \mathbf 1_{\chi\ \text{principal}}\frac1L\int_{I'} D_\gamma(\log y/L)\,dy + O(ML^{-A_1})$. (10.15) The constant may depend on the displayed fixed parameters and on $\gamma, w_-, w_+$, but the estimate is uniform in the interval and character.” On p. 67: “Put $M = H_m$ and write $R_\gamma(m) = \mathbf 1_{P^-(m) > x^\gamma}$.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 68, proof of Proposition 10.3, (10.15)

import Mathlib
import Definitions.Def_ArtinSieve

namespace ArtinPrimitiveRoots

open Real

open Classical in
theorem rough_prime_product_count (γ wMinus wPlus : ℝ) (hγ : 0 < γ) (hγw : γ < wMinus)
    (hww : wMinus < wPlus) (hwPlus : wPlus < 1) :
    ∀ A₀ A₁ : ℝ, 0 < A₀ → 0 < A₁ →
      ∃ K x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ M : ℝ, 0 < M → wMinus ≤ log M / log x → log (2 * M) / log x ≤ wPlus →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ log x ^ A₀ → ∀ χ : DirichletCharacter ℂ k,
      ∀ J : Set ℝ, J.OrdConnected → J ⊆ Set.Icc M (2 * M) →
        ‖(∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1),
            if (m : ℝ) ∈ J ∧ IsRough (x ^ γ) m then χ (m : ZMod k) else 0) -
          (if χ = 1 then
            (((1 / log x) * ∫ y in J, roughDensity γ (log y / log x) : ℝ) : ℂ)
          else 0)‖ ≤ K * (M * log x ^ (-A₁)) := by
  sorry

end ArtinPrimitiveRoots
