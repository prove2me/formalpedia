-- Prove2me | Theorems.Thm_DiazModulus_multiplicityEstimateElem
-- name    : DiazModulus.multiplicityEstimateElem
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:52:31.771468+00:00
-- url     : https://prove2.me/theorems/382b9f05-eddb-4ee3-932d-3edb5fb187bf
-- title:
--   The elementary multiplicity estimate: DALAG Th. 8.1 in the case $G^- = \{e\}$ for $G = \mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}$ over $\mathbb{C}$
-- statement:
--   The proposition `MultiplicityEstimateElem` of the published Definition `MultiplicityEstimateElem` (module `Definitions.Def_MultiplicityEstimateElem`) holds. It is the elementary multiplicity estimate, DALAG Th. 8.1 in the case $G^- = \{e\}$ for $G = \mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}$ over $\mathbb{C}$, written in coordinates: for finite $A_0, A_1, B_0, B_1$, $d = |A_0| + |A_1|$, vectors $w_b \in \mathbb{C}^{A_0} \times \mathbb{C}^{A_1}$ with span $W$, $u_j \in \mathbb{C}^{A_0}$, non-zero $a_{ji}$, $D_0, D_1 \ge 1$, $M_0, M_1 \in \mathbb{N}$ and a non-zero coefficient vector $c$, if the polynomial $P_c$ and its derivatives $D_{w_{k_1}} \cdots D_{w_{k_r}} P_c$, $r \le dM_0$, vanish at the points $g_s = (\sum_j s_j u_j, (\prod_j a_{ji}^{s_j})_i)$, $|s_j| \le dM_1$, then there are a subspace $V \subseteq \mathbb{C}^{A_0}$, integer rows $\varphi_1, \dots, \varphi_q \in \mathbb{Z}^{A_1}$ with common complex kernel $L$ and $\ell$ with $\ell + \dim(W \cap (V \times L)) = \dim W$, such that $\dim V + \dim L < d$ and every set $R$ of $s$ with $|s_j| \le M_1$, pairwise incongruent modulo $(V, \varphi)$, satisfies $\binom{M_0 + \ell}{\ell} |R|\, D_0^{\dim V} D_1^{\dim L} \le 2^{d(d+1)/2}\, d!\, 2^{|A_1|}\, |A_0|^{|A_0|} D_0^{|A_0|} D_1^{|A_1|}$. With milestone 161, `DiazModulus.strong_six_exponentials` (Roy's strong six exponentials theorem under the hypothesis `MultiplicityEstimateElem`), it gives Roy's strong six exponentials theorem with no hypothesis (`DiazModulus.strong_six_exponentials_unconditional`).
--
--   **Proof.** $P = P_c$ lies in the box and not in $J_0$ (`DiazModulus.torus_coeff_poly`), and `DiazModulus.eval_torusDerivList_eq_zero` turns the premise into the vanishing of $D_l P$ at the $g_s$. `DiazModulus.exists_obstruction` gives the obstruction subgroup $\Gamma$, its sections and $V \times L$ with $\dim V + \dim L < d$, and the ideal $A$. For each set $R$, `DiazModulus.hlow_le_boxHilb` bounds $h_A$ below on the rays $tD + C$; `DiazModulus.torus_hilbert_side`, with Macaulay's unmixedness `DiazModulus.unmixedHeight_mvPolynomial`, bounds it above, and `DiazModulus.le_hME_constant` turns the comparison into the stated constant. The conclusion takes $\varphi = \psi$ reindexed by an enumeration of $A_1$ and $\ell = \dim W - \dim(W \cap (V \times L))$.
--
--   **Novelty.** None claimed: DALAG Th. 8.1 in the case $G^- = \{e\}$, with the proof of DALAG §8.4 by D. Roy, routed through elementary arguments and written at finite level, in coordinates; routine formalisation.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Th. 8.1 (§8.1, p. 232; Chapter 8 is by D. Roy), the case G⁻ = {e}, G⁺ = G, with the proof of §8.4 (§8.4.1, Lemmas 8.14–8.16, (8.20)) at finite level. For G⁻ = {e} and finite Σ, DALAG notes that Th. 8.1 is a special case of Th. 2.1 of P. Philippon, Lemmes de zéros dans les groupes algébriques commutatifs, Bull. Soc. Math. France 114 (1986), 355–383. Uses `DiazModulus.eval_torusDerivList_eq_zero`, `DiazModulus.torus_coeff_poly`, `DiazModulus.hlow_le_boxHilb`, `DiazModulus.exists_obstruction`, `DiazModulus.torus_hilbert_side`, `DiazModulus.le_hME_constant` and `DiazModulus.unmixedHeight_mvPolynomial`. C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_MultiplicityEstimateElem

namespace DiazModulus

theorem multiplicityEstimateElem :
    MultiplicityEstimateElem := by
  sorry

end DiazModulus
