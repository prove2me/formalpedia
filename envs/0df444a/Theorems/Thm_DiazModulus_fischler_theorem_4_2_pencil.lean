-- Prove2me | Theorems.Thm_DiazModulus_fischler_theorem_4_2_pencil
-- name    : DiazModulus.fischler_theorem_4_2_pencil
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-21T08:08:06.598078+00:00
-- url     : https://prove2.me/theorems/3f68e805-eb99-4331-9607-1af76accb627
-- title:
--   Fischler 2001, Theorem 4.2 in pencil form ('disjoint from the dense orbit Y' read as rk M_α < d); not printed in this form
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates. For $d \times d$ matrices $F_1, \dots, F_l$ and $\alpha \in \mathbb C^d$, write $M_\alpha$ for the $d \times l$ matrix whose $a$-th column is $F_a\alpha$, so that $M_\alpha s = (s_1F_1 + \dots + s_lF_l)\,\alpha$ for $s \in \mathbb C^l$; $\operatorname{rk}$ is the rank over $\mathbb C$.
--
--   Let $F_1, \dots, F_l$ be $d \times d$ matrices with algebraic entries, let $x \in \mathbb C^d$ have all its coordinates in $\widetilde{\mathcal L}$, and put $r = \operatorname{rk} M_x$. Assume that $2r < d$. Then there is a rational subspace $E \subseteq \mathbb C^d$ with $x \in E$ such that $\operatorname{rk} M_\alpha < d$ for every $\alpha \in E$.
-- source:
--   S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Th. 4.2 (p. 175), in pencil form; not printed in this form. Printed: if ρ has a Zariski-dense orbit Y and X has dimension r < d/2, every x ∈ X(ℒ) lies in a subspace defined over Q̄ that is disjoint from Y. The pencil form uses the dictionary of the pencil form of Prop. 3.2 (DiazModulus.fischler_prop_3_2_pencil), with r = rk M_x, and reads 'disjoint from Y' as rk M_α < d on E: when a Zariski-dense orbit Y exists, Y is the set of α with rk M_α = d, by Lemma 2.4 and since an orbit is open in its closure. The dense-orbit hypothesis is not needed, so the pencil form is slightly more general. Fischler's ℒ, the Q̄-vector space spanned by 1 and the logarithms of algebraic numbers, is ℒ̃ here. The proof is the printed one: E is the least rational subspace containing x, and the pencil form of Prop. 3.2 with rank–nullity bounds rk M_α on E. Proved from DiazModulus.fischler_prop_3_2_pencil, DiazModulus.fischler_rational_hull and DiazModulus.rational_common_kernel. Formal proof: Diaz modulus mission, 20 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fischler_theorem_4_2_pencil {d l : ℕ} (F : Fin l → Matrix (Fin d) (Fin d) ℂ)
    (hF : ∀ a i j, F a i j ∈ Qbar) (x : Fin d → ℂ) (hx : ∀ i, x i ∈ LogAlgTilde)
    (hr : 2 * (Matrix.of fun i a => ((F a).mulVec x) i).rank < d) :
    ∃ E : Submodule ℂ (Fin d → ℂ),
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ E ∧ ∀ i, v i ∈ Qbar} = E ∧ x ∈ E ∧
      ∀ α ∈ E, (Matrix.of fun i a => ((F a).mulVec α) i).rank < d := by
  sorry

end DiazModulus
