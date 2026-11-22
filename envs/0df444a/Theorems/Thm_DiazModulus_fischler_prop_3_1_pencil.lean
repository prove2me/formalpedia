-- Prove2me | Theorems.Thm_DiazModulus_fischler_prop_3_1_pencil
-- name    : DiazModulus.fischler_prop_3_1_pencil
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-21T08:07:54.102149+00:00
-- url     : https://prove2.me/theorems/8b4ba92d-787c-4036-afa8-51b9fb81f9ce
-- title:
--   Fischler 2001, Proposition 3.1 in pencil form (suitability replaced by its linear consequences (S1′)–(S3′), dim X by rk M_x); not printed in this form
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates. For $u, v \in \mathbb C^d$ write $u \cdot v = \sum_i u_i v_i$. For $d \times d$ matrices $F_1, \dots, F_l$ and $\alpha \in \mathbb C^d$, write $M_\alpha$ for the $d \times l$ matrix whose $a$-th column is $F_a\alpha$, so that $M_\alpha s = (s_1F_1 + \dots + s_lF_l)\,\alpha$ for $s \in \mathbb C^l$; $\operatorname{rk}$ is the rank over $\mathbb C$.
--
--   Let $F_1, \dots, F_l$ be $d \times d$ matrices with algebraic entries, let $x \in \mathbb C^d$ have all its coordinates in $\widetilde{\mathcal L}$, and put $r = \operatorname{rk} M_x$. Assume
--
--   (S1′) $F_1, \dots, F_l$ are linearly independent over $\overline{\mathbb Q}$;
--
--   (S2′) no non-zero $\varphi \in \mathbb C^d$ with algebraic coordinates satisfies $\varphi^{\mathsf T} F_a = 0$ for $a = 1, \dots, l$;
--
--   (S3′) $(d + l)\,r < dl$.
--
--   Assume also that $x$ lies in no hyperplane defined over $\overline{\mathbb Q}$: $\varphi \cdot x \neq 0$ for every non-zero $\varphi \in \mathbb C^d$ with algebraic coordinates. Then there are subspaces $S \subseteq \mathbb C^l$ and $T \subseteq \mathbb C^d$ and a natural number $r_1$ such that, with $l_1 = l - \dim S$ and $d_1 = d - \dim T$, we have $l_1 \ge 1$, $d_1 \ge 1$, $(s_1F_1 + \dots + s_lF_l)\,\alpha \in T$ for every $s \in S$ and every $\alpha \in \mathbb C^d$ (the image of $s_1F_1 + \dots + s_lF_l$ lies in $T$), $r_1 \ge 1$, and
--   $$r_1 d < r d_1 \quad\text{and}\quad l_1 d_1 \le r_1 (l_1 + d_1),$$
--   that is, $r_1/d_1 < r/d$ and $r_1 \ge l_1 d_1/(l_1 + d_1)$. $S$ and $T$ are not required to be rational, as in print.
-- source:
--   S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Prop. 3.1 (p. 173), in pencil form; not printed in this form, with the dictionary of the pencil form of Prop. 3.2 (DiazModulus.fischler_prop_3_2_pencil). The printed hypothesis that (ρ, X) is suitable (p. 172) is replaced by its linear consequences: Lie(ρ) injective gives (S1′); the condition that no open subgroup of G^op fixes a non-zero φ in W* gives (S2′) in the complex case, through the exponential, and the printed proof uses it only for algebraic φ; r < dl/(d + l) is (S3′) with r = rk M_x (Lemma 2.4). Hyperplanes are vector hyperplanes (convention of p. 169). As printed, S and T are not said to be defined over Q̄. Fischler's ℒ, the Q̄-vector space spanned by 1 and the logarithms of algebraic numbers, is ℒ̃ here. The proof is the printed one (pp. 173–174): Fischler's Th. 2.1 applied to M_x, whose columns and rows are Q̄-free by (S1′), (S2′) and the hypothesis on x. Proved from DiazModulus.fischler_theorem_2_1 and DiazModulus.rational_common_kernel. Formal proof: Diaz modulus mission, 20 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fischler_prop_3_1_pencil {d l : ℕ} (F : Fin l → Matrix (Fin d) (Fin d) ℂ)
    (hF : ∀ a i j, F a i j ∈ Qbar) (hinj : LinearIndependent (↥Qbar) F)
    (hfix : ∀ φ : Fin d → ℂ, (∀ i, φ i ∈ Qbar) → (∀ a, Matrix.vecMul φ (F a) = 0) → φ = 0)
    (x : Fin d → ℂ) (hx : ∀ i, x i ∈ LogAlgTilde)
    (hhyp : ∀ φ : Fin d → ℂ, (∀ i, φ i ∈ Qbar) → φ ⬝ᵥ x = 0 → φ = 0)
    (hr : (d + l) * (Matrix.of fun i a => ((F a).mulVec x) i).rank < d * l) :
    ∃ (S : Submodule ℂ (Fin l → ℂ)) (T : Submodule ℂ (Fin d → ℂ)) (r₁ : ℕ),
      1 ≤ l - Module.finrank ℂ ↥S ∧ 1 ≤ d - Module.finrank ℂ ↥T ∧
      (∀ s ∈ S, ∀ α : Fin d → ℂ, (∑ a, s a • F a).mulVec α ∈ T) ∧ 1 ≤ r₁ ∧
      r₁ * d < (Matrix.of fun i a => ((F a).mulVec x) i).rank * (d - Module.finrank ℂ ↥T) ∧
      (l - Module.finrank ℂ ↥S) * (d - Module.finrank ℂ ↥T) ≤
        r₁ * ((l - Module.finrank ℂ ↥S) + (d - Module.finrank ℂ ↥T)) := by
  sorry

end DiazModulus
