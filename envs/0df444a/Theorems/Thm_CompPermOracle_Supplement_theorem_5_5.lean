-- Prove2me | Theorems.Thm_CompPermOracle_Supplement_theorem_5_5
-- name    : CompPermOracle.Supplement.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:49:46.161701+00:00
-- url     : https://prove2.me/theorems/05f3edb0-b296-46f8-9f72-f12da177ede8
-- title:
--   Theorem 5.5 — explicit sponge preimage and collision security
-- statement:
--   Let the sponge have rate $r\ge1$, capacity $c\ge1$ and digest length $1\le d\le r$, built on a uniformly random permutation $\varphi$ of $\{0,1\}^{r+c}$, so $N=2^{r+c}$; messages are mapped to nonempty sequences of rate blocks by an injective padding rule. Consider a quantum algorithm making $q$ forward and/or inverse swap queries to $\varphi$ that outputs one candidate message (preimage finding, for a target $w\in\{0,1\}^d$ fixed independently of $\varphi$) or two candidate messages (collision finding), and let $L\ge1$ bound the total number of padded blocks in its output. Put $T=q+2L$. If $3T-1\le N$, then
--   $$
--   p_{\mathrm{pre}}\le\Big[a_N(T)\Big(\frac{2\sqrt2\,T}{2^{d/2}}+\frac{4T^{3/2}}{2^{c/2}}\Big)+e_N(T)\Big]^2,\qquad
--   p_{\mathrm{col}}\le\Big[a_N(T)\Big(\frac{4\sqrt2\,T^{3/2}}{3\cdot2^{d/2}}+\frac{4T^{3/2}}{2^{c/2}}\Big)+e_N(T)\Big]^2 .
--   $$
--   If $1\le T\le 2^{(r+c)/2}/4$, then
--   $$
--   p_{\mathrm{pre}}\le\frac{64T^2}{2^d}+\frac{128T^3}{2^c}+\frac{32768T^2}{2^{r+c}},\qquad
--   p_{\mathrm{col}}\le\frac{32T^3}{2^d}+\frac{128T^3}{2^c}+\frac{32768T^2}{2^{r+c}} .
--   $$
--   Here $p_{\mathrm{pre}}$ is the probability that the sponge digest of the output message equals $w$, and $p_{\mathrm{col}}$ the probability that the two output messages are distinct and have equal digests.
--
--   These bounds give concrete post-quantum preimage and collision security of the sponge (and hence of SHA-3 in the random permutation model) against adversaries with forward and inverse access, with explicit dependence on the output length.
--
--   **Formalization Note** The sponge, its digest and the error terms $a_N$, $e_N$ are the supplement's definitions; the algorithm is the published `Alg`.
--
--   Differences from the source:
--   - generalization: messages are bit strings, padded by a fixed unambiguous (injective) padding rule into nonempty block sequences → any message type M with any injective pad : M → List (Fin r → Bool) whose values are nonempty; reason: the source's bit strings with SHA-3's (or any injective) encoding are an instance
--   - generalization: states {0,1}^{r+c} queried as the permutation's domain of size N = 2^{r+c} → states (Fin r → Bool) × (Fin c → Bool), identified with Fin N by an arbitrary equivalence e, quantified universally; reason: every fixed bit encoding of the source is one such e; the statement for all e specializes to it
--   - encoding: an algorithm making q queries and outputting one or two candidate messages; L ≥ 1 bounds the total number of padded blocks in its output → a published Alg run for q queries with an output map out : Acc → M (resp. M × M), with the padded length (resp. the sum of both padded lengths) ≤ L for every outcome, and 1 ≤ L; reason: a measured output is a function of the computational-basis outcome
--   - encoding: 1 ≤ T ≤ 2^{(r+c)/2}/4 for (94), (95), under the theorem's standing 3T − 1 ≤ N → (T : ℝ) ≤ 2^{(r+c)/2}/4 alone, without 1 ≤ T and without 3T − 1 ≤ N; reason: T = q + 2L ≥ 2 always, and T ≤ √N/4 implies 3T − 1 ≤ N, so neither omitted condition excludes an instance
--   - encoding: 3T − 1 ≤ N; T^{3/2}, 2^{d/2}, 2^{c/2}, 2^{(r+c)/2} → 3 * T ≤ N + 1 in ℕ; real powers (Real.rpow); all differences in ℝ; reason: same instances; r + c may be odd
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), Theorem 5.5, eqs. (91)–(95), p.31 (sponge: §3.5, p.10; digest: §5.3, p.30)

import Mathlib
import Definitions.Def_CompPermOracle_Alg
import Definitions.Def_CompPermOracle_Supplement_deltaN
import Definitions.Def_CompPermOracle_Supplement_keyedState
import Definitions.Def_CompPermOracle_Supplement_sponge

namespace CompPermOracle.Supplement

open CompPermOracle

/-- **Theorem 5.5 (Explicit sponge security)** (Carolan, Majenz, Compressed Permutation Oracles
Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), Theorem 5.5, eqs. (92)–(95),
p.31). Let `1 ≤ d ≤ r`, `N = 2^{r+c}` and `T = q + 2L`. For a uniformly random permutation and
`3T − 1 ≤ N`, the fixed-target preimage and collision success probabilities satisfy (92) and (93);
if `1 ≤ T ≤ 2^{(r+c)/2}/4`, they satisfy (94) and (95).

**Formalization Note.** Capacity `c ≥ 1` (§3.5, p.10); the rate bound `r ≥ 1` follows from `1 ≤ d ≤ r`. Messages are any type `M`
with an injective padding `pad` into nonempty lists of rate blocks (p.31: "the padding rule is
assumed injective"). The sponge states (rate bits, capacity bits) are identified with `Fin N` by an
arbitrary equivalence `e`, quantified universally. The algorithm makes `q` forward/inverse swap
queries and outputs one message (preimage) or two messages (collision), through an output map; `L`
bounds the total number of padded blocks of the output for every outcome. The target `w ∈ {0,1}^d`
is fixed before the permutation is sampled. Collision success requires distinct messages with equal
digests. `T^{3/2}` and `2^{x/2}` are real powers. The source's `1 ≤ T` in the second part always
holds (`T = q + 2L`, `L ≥ 1`) and is omitted. -/
theorem theorem_5_5 {r c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d) (hdr : d ≤ r) {N : ℕ}
    (hN : N = 2 ^ (r + c)) (e : (Fin r → Bool) × (Fin c → Bool) ≃ Fin N) {M : Type}
    (pad : M → List (Fin r → Bool)) (hpad : Function.Injective pad) (hne : ∀ m, pad m ≠ [])
    {W : Type} [Fintype W] [DecidableEq W] (A : Alg N W) (q L T : ℕ) (hL : 1 ≤ L)
    (hT : T = q + 2 * L) :
    (∀ (w : Fin d → Bool) (out : Acc N W → M), (∀ c', (pad (out c')).length ≤ L) →
      (3 * T ≤ N + 1 →
        realSuccess A q out (fun m φ => spongeDigest hdr e φ (pad m) = w) ≤
          (aN N T * (2 * Real.sqrt 2 * T / (2 : ℝ) ^ ((d : ℝ) / 2) +
              4 * (T : ℝ) ^ ((3 : ℝ) / 2) / (2 : ℝ) ^ ((c : ℝ) / 2)) + eN N T) ^ 2) ∧
      ((T : ℝ) ≤ (2 : ℝ) ^ (((r + c : ℕ) : ℝ) / 2) / 4 →
        realSuccess A q out (fun m φ => spongeDigest hdr e φ (pad m) = w) ≤
          64 * (T : ℝ) ^ 2 / (2 : ℝ) ^ d + 128 * (T : ℝ) ^ 3 / (2 : ℝ) ^ c +
            32768 * (T : ℝ) ^ 2 / (2 : ℝ) ^ (r + c))) ∧
    (∀ out : Acc N W → M × M, (∀ c', (pad (out c').1).length + (pad (out c').2).length ≤ L) →
      (3 * T ≤ N + 1 →
        realSuccess A q out
            (fun mm φ => mm.1 ≠ mm.2 ∧
              spongeDigest hdr e φ (pad mm.1) = spongeDigest hdr e φ (pad mm.2)) ≤
          (aN N T * (4 * Real.sqrt 2 * (T : ℝ) ^ ((3 : ℝ) / 2) / (3 * (2 : ℝ) ^ ((d : ℝ) / 2)) +
              4 * (T : ℝ) ^ ((3 : ℝ) / 2) / (2 : ℝ) ^ ((c : ℝ) / 2)) + eN N T) ^ 2) ∧
      ((T : ℝ) ≤ (2 : ℝ) ^ (((r + c : ℕ) : ℝ) / 2) / 4 →
        realSuccess A q out
            (fun mm φ => mm.1 ≠ mm.2 ∧
              spongeDigest hdr e φ (pad mm.1) = spongeDigest hdr e φ (pad mm.2)) ≤
          32 * (T : ℝ) ^ 3 / (2 : ℝ) ^ d + 128 * (T : ℝ) ^ 3 / (2 : ℝ) ^ c +
            32768 * (T : ℝ) ^ 2 / (2 : ℝ) ^ (r + c))) := by sorry

end CompPermOracle.Supplement
