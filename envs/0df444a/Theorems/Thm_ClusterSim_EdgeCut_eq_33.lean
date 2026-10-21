-- Prove2me | Theorems.Thm_ClusterSim_EdgeCut_eq_33
-- name    : ClusterSim.EdgeCut.eq_33
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:53:49.124635+00:00
-- url     : https://prove2.me/theorems/5272c4f1-50be-4f0f-b004-1d879a80de98
-- title:
--   Eq. (33) with |c_s| = 2^{−K} — T(G, A) = E_s[8^K c_s T(G′, A_s)] for s uniform on [8]^C
-- statement:
--   Let $(G,\mathcal A)$ be a tensor network, $C$ a finite set of $K=|C|$ edges, and $c_s$, $(G',\mathcal A_s)$ as in eqs. (31)–(32). Regarding $s$ as uniformly distributed on $[8]^C$ (each of the $8^K$ strings has probability $8^{-K}$),
--   $$T(G,\mathcal A)=\mathbb E_s\big[8^K c_s\,T(G',\mathcal A_s)\big]=\sum_{s\in[8]^C}8^{-K}\cdot 8^K c_s\,T(G',\mathcal A_s),$$
--   and every coefficient has absolute value
--   $$|c_s|=\prod_{e\in C}|c_{s_e}|=2^{-K}.$$
--
--   The second fact is what bounds the samples of the simulation by $8^K\cdot2^{-K}=2^{2K}$ (eq. (36)).
-- source:
--   Peng, Harrow, Ozols & Wu, Simulating Large Quantum Circuits on a Small Quantum Computer, arXiv:1904.00102v2, p. 9, proof of Theorem 1, eq. (33); |c_s| = 1/2^K stated on p. 10 under eq. (36)

import Mathlib
import Definitions.Def_ClusterSim_EdgeCut_Cut

namespace ClusterSim.EdgeCut

/-- Eq. (33), p. 9, with `|c_s| = 1/2^K` (p. 10, under eq. (36)): with `K = |C|` and `s` uniform on
`[8]^C` (weight `8^{-K}` per string), `T(G, A) = E_s[8^K c_s T(G′, A_s)]`, and every coefficient
has `|c_s| = 2^{-K}`. -/
theorem eq_33 (G : TensorNetwork) (C : Finset G.E) :
    value G = ∑ s : C → Fin 8,
        ((8 : ℂ) ^ C.card)⁻¹ * ((8 : ℂ) ^ C.card * (coefS s : ℂ) * value (cut G C s)) ∧
      ∀ s : C → Fin 8, |coefS s| = 1 / 2 ^ C.card := by sorry

end ClusterSim.EdgeCut
