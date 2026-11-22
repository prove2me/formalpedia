-- Prove2me | Theorems.Thm_DiazModulus_fischler_theorem_4_1_pencil
-- name    : DiazModulus.fischler_theorem_4_1_pencil
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-21T08:08:05.569163+00:00
-- url     : https://prove2.me/theorems/bb3c0f5d-2dc5-4668-9471-84525238f6cb
-- title:
--   Fischler 2001, Theorem 4.1 in pencil form (orbit dimensions read as ranks of M_α, M_x; suitability as in the pencil form of Prop. 3.1); not printed in this form
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates. For $u, v \in \mathbb C^d$ write $u \cdot v = \sum_i u_i v_i$. For $d \times d$ matrices $F_1, \dots, F_l$ and $\alpha \in \mathbb C^d$, write $M_\alpha$ for the $d \times l$ matrix whose $a$-th column is $F_a\alpha$, so that $M_\alpha s = (s_1F_1 + \dots + s_lF_l)\,\alpha$ for $s \in \mathbb C^l$; $\operatorname{rk}$ is the rank over $\mathbb C$.
--
--   Let $k \ge 2$. Let $F_1, \dots, F_l$ be $d \times d$ matrices with algebraic entries, let $x \in \mathbb C^d$ have all its coordinates in $\widetilde{\mathcal L}$, and put $r = \operatorname{rk} M_x$. Assume
--
--   (S1′) $F_1, \dots, F_l$ are linearly independent over $\overline{\mathbb Q}$;
--
--   (S2′) no non-zero $\varphi \in \mathbb C^d$ with algebraic coordinates satisfies $\varphi^{\mathsf T} F_a = 0$ for $a = 1, \dots, l$;
--
--   (S3′) $(d + l)\,r < dl$.
--
--   Assume also that $d < \operatorname{rk} M_\alpha + k$ for some $\alpha \in \mathbb C^d$, and that $k r \le d$. Then $x$ lies in a hyperplane defined over $\overline{\mathbb Q}$: there is a non-zero $\varphi \in \mathbb C^d$ with algebraic coordinates such that $\varphi \cdot x = 0$.
-- source:
--   S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Th. 4.1 (pp. 174–175), in pencil form; not printed in this form, with the dictionary of the pencil form of Prop. 3.2 (DiazModulus.fischler_prop_3_2_pencil). The printed hypotheses (k > 1; (ρ, X) suitable; a ρ-orbit of codimension less than k in W; X of dimension r ≤ d/k) become k ≥ 2, (S1′)–(S3′) as in the pencil form of Prop. 3.1, d − rk M_α < k for some α, and k·rk M_x ≤ d, orbit dimensions being read as ranks (Lemma 2.4). Hyperplanes are vector hyperplanes (convention of p. 169). Fischler's ℒ, the Q̄-vector space spanned by 1 and the logarithms of algebraic numbers, is ℒ̃ here. The proof is the printed one (p. 175), its arithmetic cleared of denominators. Proved from DiazModulus.fischler_prop_3_1_pencil. Formal proof: Diaz modulus mission, 20 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fischler_theorem_4_1_pencil {d l k : ℕ} (hk : 2 ≤ k) (F : Fin l → Matrix (Fin d) (Fin d) ℂ)
    (hF : ∀ a i j, F a i j ∈ Qbar) (hinj : LinearIndependent (↥Qbar) F)
    (hfix : ∀ φ : Fin d → ℂ, (∀ i, φ i ∈ Qbar) → (∀ a, Matrix.vecMul φ (F a) = 0) → φ = 0)
    (α : Fin d → ℂ) (hα : d < (Matrix.of fun i a => ((F a).mulVec α) i).rank + k)
    (x : Fin d → ℂ) (hx : ∀ i, x i ∈ LogAlgTilde)
    (hr : (d + l) * (Matrix.of fun i a => ((F a).mulVec x) i).rank < d * l)
    (hrk : k * (Matrix.of fun i a => ((F a).mulVec x) i).rank ≤ d) :
    ∃ φ : Fin d → ℂ, (∀ i, φ i ∈ Qbar) ∧ φ ≠ 0 ∧ φ ⬝ᵥ x = 0 := by
  sorry

end DiazModulus
