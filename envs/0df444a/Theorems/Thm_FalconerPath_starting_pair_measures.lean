-- Prove2me | Theorems.Thm_FalconerPath_starting_pair_measures
-- name    : FalconerPath.starting_pair_measures
-- status  : Open
-- author  : @dangnguyen
-- created : 2026-11-03T20:20:38.418196+00:00
-- url     : https://prove2.me/theorems/adff0a67-fe34-41ca-8e09-62c947e531a1
-- title:
--   Starting pair measures in the original dimension
-- statement:
--   Let $d\ge2$, let $E\subset\mathbb R^d$ be compact with $\dim_H E>S=d/2$, and fix a patch radius $r>0$. Either $\Delta(E)$ has positive Lebesgue measure, or there are compact sets $E_1,E_2\subset E$ separated by a positive distance, probabilities $\mu_i$ carried by $E_i$, constants $\chi,C>0$ with $\mu_i(B(z,u))\le Cu^{S+\chi}$ for every center and $0<u\le1$, and a unit $w$ such that $\pi_x(y)\in B(w,r)$ for all $x\in E_1,y\in E_2$.
--
--   These choices precede a cutoff $0<\omega_0\le1$ such that for every $0<\omega\le\omega_0$ there are decreasing Borel $\Gamma_N\subset E_1\times E_2$ with positive product mass in $\bigcap_N\Gamma_N$, and a constant $C_\omega>0$ giving disjoint spatial product partitions of each $\Gamma_N$ with at most $C_\omega2^{2d\omega N}$ pieces. For every $e>0$ there are $c_e,C_e>0$ and $N_0$ such that each $N\ge N_0$ admits a Borel $B_N\subset\Gamma_N$ with product mass at most $C_e2^{-c_eN}$, and both unnormalized directional laws of $\Gamma_N\setminus B_N$ give every radius-$u$ cap mass at most $2^{eN}u^S$ for $2^{-N}\le u\le1$, at almost every corresponding pin.
--
--   Lean states the first alternative directly as positive distance measure, keeps the second alternative in original coordinates by undoing the paper's similarity, and expresses null-fiber removal almost everywhere.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf. Section 5.4, Proposition 5.10 (Starting pair measures), label prep:starting-pairs, including clauses (i), (ii), and (iii) and the parameter-order paragraph. See also Remark 5.11 (Order of parameters), label prep:parameters.

import Definitions.Def_FalconerPath_defs
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FalconerPath
theorem starting_pair_measures {d : ℕ} (hd : 2 ≤ d)
    (E : Set (Space d)) (hE : IsCompact E)
    (hdim : (d : ℝ≥0∞)/2 < dimH E) (patchRadius : ℝ) (hpatch : 0 < patchRadius) :
    0 < volume (distanceSet E) ∨ Nonempty (StartingPair d E patchRadius) := by sorry
end FalconerPath
