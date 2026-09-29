-- Prove2me | Theorems.Thm_DiazModulus_two_three_five_pow_pi_transcendental
-- name    : DiazModulus.two_three_five_pow_pi_transcendental
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T16:29:52.922882+00:00
-- url     : https://prove2.me/theorems/8341ef99-ebe6-4a09-9c30-c5cb3a04ff16
-- title:
--   At least one of 2^π, 3^π and 5^π is transcendental
-- statement:
--   **$2^{\pi}$, $3^{\pi}$ or $5^{\pi}$.**
--
--   At least one of the three real numbers
--
--   $$2^{\pi}, \qquad 3^{\pi}, \qquad 5^{\pi}$$
--
--   is transcendental.
--
--   For a single one of them this is open. For a pair more is known than this node states: by the five exponentials theorem, at least one of $2^{\pi}$ and $3^{\pi}$ is transcendental (M. Waldschmidt, *On the transcendence methods of Gel'fond and Schneider in several variables*, in *New Advances in Transcendence Theory*, Cambridge 1988, statement (2.2.3) with $t = \pi$ and $\beta = i$, where $e^{i\pi} = -1$). The five exponentials theorem has no formal proof in this environment; this node records what the formalised six exponentials theorem reaches. Three numbers are what the six exponentials theorem of Lang and Ramachandra reaches, applied to $x = (1, \pi)$ and $y = (\log 2, \log 3, \log 5)$: the $x_i$ are $\mathbb{Q}$-linearly independent because $\pi$ is irrational, and the $y_j$ because of unique factorisation. The companion statement `DiazModulus.sixExponentials_cannot_refute_candidate` explains why the same theorem cannot reach Diaz's conjecture: a candidate certifies a three-dimensional space, and a $2 \times 3$ configuration needs more room.
--
--   **Novelty.** None: a classical consequence of the six exponentials theorem (Lang 1966; Ramachandra 1968), and weaker than the pair statement above. The contribution of this node is the formal proof.
-- source:
--   Classical: S. Lang, Introduction to Transcendental Numbers, Addison-Wesley, 1966, chapter II; K. Ramachandra, Contributions to the theory of transcendental numbers I, II, Acta Arith. 14 (1968). Stronger known form (one of 2^pi, 3^pi): M. Waldschmidt, On the transcendence methods of Gel'fond and Schneider in several variables, in New Advances in Transcendence Theory (Durham, 1986), Cambridge Univ. Press, 1988, 375–398, (2.2.3). Formal proof: Diaz modulus mission, 23 September 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem two_three_five_pow_pi_transcendental :
    Transcendental ℚ ((2 : ℝ) ^ Real.pi) ∨ Transcendental ℚ ((3 : ℝ) ^ Real.pi) ∨
      Transcendental ℚ ((5 : ℝ) ^ Real.pi) := by sorry

end DiazModulus
