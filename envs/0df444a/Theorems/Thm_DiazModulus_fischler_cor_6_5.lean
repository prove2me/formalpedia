-- Prove2me | Theorems.Thm_DiazModulus_fischler_cor_6_5
-- name    : DiazModulus.fischler_cor_6_5
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-21T08:08:07.224809+00:00
-- url     : https://prove2.me/theorems/a96ad673-8e22-4e26-bd60-05da04cc1d48
-- title:
--   Fischler 2001, Cor. 6.5 (1): for k ≥ 3, every v ⊗ ⋯ ⊗ v with coordinates in ℒ̃ lies on a line ℂy with y algebraic, made of tensors v″ ⊗ ⋯ ⊗ v″ (k factors)
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   For $v \in \mathbb C^m$ and a map $I : \{1, \dots, k\} \to \{1, \dots, m\}$ write $v_I = v_{I(1)} v_{I(2)} \cdots v_{I(k)}$; these are the coordinates of $v \otimes \cdots \otimes v$ ($k$ factors) in the basis $e_{I(1)} \otimes \cdots \otimes e_{I(k)}$ of $(\mathbb C^m)^{\otimes k}$, which is defined over $\overline{\mathbb Q}$.
--
--   Let $k \ge 3$, $m \ge 0$ and $v \in \mathbb C^m$, and suppose that $v_I \in \widetilde{\mathcal L}$ for every map $I : \{1, \dots, k\} \to \{1, \dots, m\}$. Then there is a family $y = (y_I)_I$ of algebraic numbers, indexed by these maps, such that $(v_I)_I$ lies in $\mathbb C y$, and every element of $\mathbb C y$ is of the form $(v''_I)_I$ for some $v'' \in \mathbb C^m$, that is, $\mathbb C y$ consists of tensors $v'' \otimes \cdots \otimes v''$.
--
--   So every $v \otimes \cdots \otimes v$ ($k$ factors) whose coordinates lie in $\widetilde{\mathcal L}$ lies on a line (or the point $0$) defined over $\overline{\mathbb Q}$ and contained in the set $\mathcal T(k, m)$ of such tensors: the non-trivial inclusion of Fischler's Conjecture 1 for $\mathcal T(k, m)$.
-- source:
--   S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Cor. 6.5, part 1 (p. 185): Conjecture 1 (p. 168) for 𝒯(k, m) = {v ⊗ ⋯ ⊗ v} (p. 179), k ≥ 3, in the coordinates of the basis e_I(1) ⊗ ⋯ ⊗ e_I(k), which is defined over Q̄ (p. 170), in the form of its non-trivial inclusion, with a vector line ℂy as the affine subspace defined over Q̄; the other inclusion is immediate. Here for any m; Th. 6.4, on which it rests, is printed for m ≥ 2. Fischler's ℒ, the Q̄-vector space spanned by 1 and the logarithms of algebraic numbers, is ℒ̃ here. Part 2, a conditional reduction to 𝒯(2, 2), is not formalised. Proved from DiazModulus.fischler_theorem_6_4_one. Formal proof: Diaz modulus mission, 20 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fischler_cor_6_5 {m k : ℕ} (hk : 3 ≤ k) (v : Fin m → ℂ)
    (hv : ∀ I : Fin k → Fin m, ∏ t, v (I t) ∈ LogAlgTilde) :
    ∃ y : (Fin k → Fin m) → ℂ, (∀ I, y I ∈ Qbar) ∧
      (fun I : Fin k → Fin m => ∏ t, v (I t)) ∈ Submodule.span ℂ {y} ∧
      ∀ x ∈ Submodule.span ℂ {y}, ∃ v'' : Fin m → ℂ, x = fun I => ∏ t, v'' (I t) := by
  sorry

end DiazModulus
