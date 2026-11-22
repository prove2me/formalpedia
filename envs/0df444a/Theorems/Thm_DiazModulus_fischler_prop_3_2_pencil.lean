-- Prove2me | Theorems.Thm_DiazModulus_fischler_prop_3_2_pencil
-- name    : DiazModulus.fischler_prop_3_2_pencil
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-21T08:07:55.519581+00:00
-- url     : https://prove2.me/theorems/70501f73-cb02-4414-9781-43862eae1d78
-- title:
--   Fischler 2001, Proposition 3.2 in pencil form (Lie(ρ) replaced by algebraic matrices F₁, …, F_l, dim X by rk M_x); not printed in this form
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates. For $d \times d$ matrices $F_1, \dots, F_l$ and $\alpha \in \mathbb C^d$, write $M_\alpha$ for the $d \times l$ matrix whose $a$-th column is $F_a\alpha$, so that $M_\alpha s = (s_1F_1 + \dots + s_lF_l)\,\alpha$ for $s \in \mathbb C^l$; $\operatorname{rk}$ is the rank over $\mathbb C$.
--
--   Let $d \ge 1$. Let $F_1, \dots, F_l$ be $d \times d$ matrices with algebraic entries, let $x \in \mathbb C^d$ have all its coordinates in $\widetilde{\mathcal L}$, and put $r = \operatorname{rk} M_x$. Let $\mathcal E$ be the intersection of all rational subspaces of $\mathbb C^d$ that contain $x$. Then there are subspaces $S \subseteq \mathbb C^l$ and $T \subseteq \mathbb C^d$ such that, with $l_1 = l - \dim S$ and $d_1 = d - \dim T$, we have $d_1 \ge 1$,
--   $$(d - r)\,l_1 \le r\,d_1,$$
--   and $(s_1F_1 + \dots + s_lF_l)\,\alpha \in T$ for every $s \in S$ and every $\alpha \in \mathcal E$. No bound on $l_1$ is asserted, and $S$ and $T$ are not required to be rational, as in print.
-- source:
--   S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Prop. 3.2 (p. 174), in pencil form; not printed in this form. Fischler's setting (§2.3, pp. 171–172): ρ : G → GL(W) a representation of an affine algebraic group, both defined over Q̄, X an orbit, d = dim W, l = dim G, r = dim X, f_A = Lie(ρ)(A) and M_α(A) = f_A(α). The pencil form replaces Lie(ρ) by the algebraic matrices F₁, …, F_l, the images of a basis of the Lie algebra defined over Q̄ (so f_A = Σₐ sₐFₐ for A = Σₐ sₐAₐ), and dim X by rk M_x, which is Fischler's Lemma 2.4; the printed statement follows from the pencil form with Lemma 2.4. No property of the Fₐ beyond being algebraic is assumed, and x ∈ X(ℒ) becomes x ∈ ℒ̃ᵈ: the printed proof uses nothing more. 𝓔, the minimal subspace defined over Q̄ that contains x, is written as the intersection of all rational subspaces containing x; d ≥ 1 is implicit in print (d₁ ≥ 1). As printed, l₁ ≥ 0 and S, T are not said to be defined over Q̄. Fischler's ℒ, the Q̄-vector space spanned by 1 and the logarithms of algebraic numbers, is ℒ̃ here. The proof is the printed one: Roy's Cor. 1 (Fischler's Cor. 2.2) applied to M_x. Proved from DiazModulus.roy_rank_bound and DiazModulus.fischler_rational_hull. Formal proof: Diaz modulus mission, 20 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fischler_prop_3_2_pencil {d l : ℕ} (hd : 0 < d) (F : Fin l → Matrix (Fin d) (Fin d) ℂ)
    (hF : ∀ a i j, F a i j ∈ Qbar) (x : Fin d → ℂ) (hx : ∀ i, x i ∈ LogAlgTilde) :
    ∃ (S : Submodule ℂ (Fin l → ℂ)) (T : Submodule ℂ (Fin d → ℂ)),
      1 ≤ d - Module.finrank ℂ ↥T ∧
      (d - (Matrix.of fun i a => ((F a).mulVec x) i).rank) * (l - Module.finrank ℂ ↥S) ≤
        (Matrix.of fun i a => ((F a).mulVec x) i).rank * (d - Module.finrank ℂ ↥T) ∧
      ∀ s ∈ S, ∀ α ∈ sInf {E : Submodule ℂ (Fin d → ℂ) |
          Submodule.span ℂ {v : Fin d → ℂ | v ∈ E ∧ ∀ i, v i ∈ Qbar} = E ∧ x ∈ E},
        (∑ a, s a • F a).mulVec α ∈ T := by
  sorry

end DiazModulus
