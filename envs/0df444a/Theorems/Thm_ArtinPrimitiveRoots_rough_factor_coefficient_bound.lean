-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_rough_factor_coefficient_bound
-- name    : ArtinPrimitiveRoots.rough_factor_coefficient_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T14:19:33.567922+00:00
-- url     : https://prove2.me/theorems/be9c17c9-90c2-407c-9cdb-7777b2d0b845
-- title:
--   Proof of Proposition 10.3 (OpenAI) — the rough-factor coefficient satisfies the character-twisted cancellation (10.6)
-- statement:
--   Fix $C > 0$ and $0 < \gamma < w_- < w_+ < 1$, and write $L = \log x$, $W = \exp(L^{0.24})$ (`sieveLevel x`), and $V(W) = \prod_{p \le W}(1 - 1/p)$ (`mertensProduct`). For an interval $J \subseteq [H_m, 2H_m]$ and a real $v$, let
--
--   $$\alpha_m = \mathbf 1_J(m)\, m^{iv}\Bigl(\mathbf 1_{P^-(m) > x^\gamma} - \frac{D_\gamma(\log m/L)}{L\,V(W)}\,\mathbf 1_{P^-(m) > W}\Bigr),$$
--
--   the coefficient (10.13) of Proposition 10.3. Here $D_\gamma$ is the rough-number density `roughDensity`, and $P^-(m) > y$ means that every prime factor of $m$ exceeds $y$ (`IsRough y m`).
--
--   Then for all $A_0, B, A > 0$ there are $C'$ and $x_0$ such that for every $x \ge x_0$, every $H_m$ with $w_- \le \log H_m/L$ and $\log(2H_m)/L \le w_+$, every such interval $J$, every $|v| \le L^C$, every Dirichlet character $\chi$ modulo $k$ with $1 \le k \le L^{A_0}$, and every real $t$ with $|t| \le xL^B$,
--
--   $$\Bigl|\frac1{H_m}\sum_{m \le 2H_m}\alpha_m\,\chi(m)\,m^{it}\Bigr| \ \le\ C' L^{-A}.$$
--
--   $C'$ and $x_0$ depend on $A_0, B, A, C, \gamma, w_\pm$, and are uniform in $H_m$, $J$, $v$, $\chi$ and $t$.
--
--   **Formalization note.** The paper's frequency range in (10.6) is $|t| \le 2XL^B$ with $X = H_mH_n \asymp x$. Since $X \le c_2 x$ for a fixed $c_2$, the range $|t| \le xL^B$ with every fixed $B$ covers it. This statement is the claim verified in the paper's proof of Proposition 10.3. The proof of Lemma 12.1 cites it ("By the proof of Proposition 10.3"), which is why it is published on its own: Proposition 10.3 as stated has no character twist on $m$.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 67, proof of Proposition 10.3: “We verify (10.6) for this coefficient. At low frequencies the two principal counting terms cancel. At higher frequencies the prime-product sequence and the $W$-rough comparison sequence are each small.” Condition (10.6), p. 64, in Lemma 10.2: “Suppose that for every fixed $A_0, B, A > 0$, every Dirichlet character $\chi$ modulo $k \le L^{A_0}$, and every $|t| \le 2XL^B$, $\Bigl|\frac1{H_m}\sum_m\alpha_m\chi(m)m^{it}\Bigr| \ll_A L^{-A}$, (10.6) uniformly in the permitted interval, character, and frequency.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 64, 67, proof of Proposition 10.3, (10.6) for the coefficient (10.13)

import Mathlib
import Definitions.Def_ArtinSieve

namespace ArtinPrimitiveRoots

open Real

open Classical in
theorem rough_factor_coefficient_bound (C γ wMinus wPlus : ℝ) (hC : 0 < C) (hγ : 0 < γ)
    (hγw : γ < wMinus) (hww : wMinus < wPlus) (hwPlus : wPlus < 1) :
    ∀ A₀ B A : ℝ, 0 < A₀ → 0 < B → 0 < A →
      ∃ C' : ℝ, ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ Hm : ℝ, wMinus ≤ log Hm / log x → log (2 * Hm) / log x ≤ wPlus →
      ∀ J : Set ℝ, J.OrdConnected → J ⊆ Set.Icc Hm (2 * Hm) →
      ∀ v : ℝ, |v| ≤ log x ^ C →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ log x ^ A₀ → ∀ χ : DirichletCharacter ℂ k,
      ∀ t : ℝ, |t| ≤ x * log x ^ B →
        ‖((1 / Hm : ℝ) : ℂ) * ∑ m ∈ Finset.range (⌊2 * Hm⌋₊ + 1),
            (if (m : ℝ) ∈ J then
              (m : ℂ) ^ (Complex.I * v) *
                ((if IsRough (x ^ γ) m then 1 else 0) -
                  ((roughDensity γ (log m / log x) /
                      (log x * mertensProduct (sieveLevel x)) : ℝ) : ℂ) *
                    (if IsRough (sieveLevel x) m then 1 else 0))
            else 0) * χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * t)‖ ≤ C' * log x ^ (-A) := by
  sorry

end ArtinPrimitiveRoots
