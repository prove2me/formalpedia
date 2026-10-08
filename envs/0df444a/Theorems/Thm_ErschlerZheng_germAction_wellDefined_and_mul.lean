-- Prove2me | Theorems.Thm_ErschlerZheng_germAction_wellDefined_and_mul
-- name    : ErschlerZheng.germAction_wellDefined_and_mul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-05T23:31:51.178027+00:00
-- url     : https://prove2.me/theorems/93bfd723-9f6a-472a-9b70-7786b85e3671
-- title:
--   p. 19 — (τ_g Φ)(x) = σΦ(x·g)σ⁻¹ does not depend on σ and is a left action of G on Π_x Ĝ_x by automorphisms
-- statement:
--   Let a group $H$ act from the right on a topological space $X$, each map $y \mapsto y \cdot h$ continuous, let $G, L \le H$ with $L$ an auxiliary group with trivial isotropy for $G$ (`IsAuxiliary`), and let $o \in X$. For a family $\Phi$ of germs, $\Phi(x)$ in the germ group at $x$ for every $x \in X$, write $\tau_g\Phi$ for `germAction L g Φ`. Then, at every point $x$ of the orbit $o \cdot G$:
--
--   1. for $g \in G$, any $\sigma \in L$ with $x \cdot \sigma = x \cdot g$ and any $h$ fixing $x \cdot g$ whose germ there is $\Phi(x \cdot g)$, $(\tau_g\Phi)(x)$ is the germ of $\sigma h \sigma^{-1}$ at $x$: the value does not depend on $\sigma$ nor on the representative of $\Phi(x \cdot g)$;
--   2. for $g \in G$, if $\Phi(y) \in \hat{\mathcal G}_y$ (= `isotropy (G ⊔ L) y`) for every $y \in o \cdot G$, then $(\tau_g\Phi)(x) \in \hat{\mathcal G}_x$;
--   3. for $g \in G$, $\tau_g(\Phi\Psi)(x) = (\tau_g\Phi)(x)\,(\tau_g\Psi)(x)$, the product of families being pointwise;
--   4. $(\tau_1\Phi)(x) = \Phi(x)$;
--   5. for $g_1, g_2 \in G$, $(\tau_{g_1g_2}\Phi)(x) = (\tau_{g_1}(\tau_{g_2}\Phi))(x)$.
--
--   Erschler and Zheng, p. 19: “The action of $G$ on $\prod_{x \in o \cdot G} \hat{\mathcal G}_x$ is given by $(\tau_g\Phi)(x) = \sigma\Phi(x \cdot g)\sigma^{-1}$, where $\sigma \in L$ satisfies $x \cdot \sigma = x \cdot g$. One readily checks that $\tau$ is a well-defined (doesn’t depend on the choice of $\sigma$) left action of $G$ on $\prod_{x \in o \cdot G} \hat{\mathcal G}_x$.”
--
--   Conjunct 1 is “well-defined”; conjuncts 4 and 5 are “left action”, with $g_2$ acting on $\Phi$ first; conjunct 2 says that $\tau_g$ maps $\prod_{x \in o \cdot G} \hat{\mathcal G}_x$ to itself. Conjunct 3, that each $\tau_g$ respects the pointwise product, is what the multiplication $(\Phi, g)(\Phi', g') = (\Phi\tau_g\Phi', gg')$ of the semidirect product $\mathcal W$ (p. 19) needs. The families are defined on all of $X$; every conclusion is at points of $o \cdot G$.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 19, the action τ

import Mathlib
import Definitions.Def_ErschlerZheng_Germs
open scoped RightActions

namespace ErschlerZheng

theorem germAction_wellDefined_and_mul {H : Type*} [Group H] {X : Type*} [TopologicalSpace X]
    [MulAction Hᵐᵒᵖ X] [ContinuousConstSMul Hᵐᵒᵖ X] (G L : Subgroup H)
    (hL : IsAuxiliary (X := X) G L) (o : X) :
    (∀ g ∈ G, ∀ Φ : (x : X) → GermGroup (H := H) x, ∀ x ∈ rightOrbit G o, ∀ σ ∈ L,
        x <• σ = x <• g → ∀ h : H, (x <• g) <• h = x <• g → germ (x <• g) h = Φ (x <• g) →
          germAction L g Φ x = germ x (σ * h * σ⁻¹)) ∧
      (∀ g ∈ G, ∀ Φ : (x : X) → GermGroup (H := H) x,
        (∀ y ∈ rightOrbit G o, Φ y ∈ isotropy (G ⊔ L) y) →
          ∀ x ∈ rightOrbit G o, germAction L g Φ x ∈ isotropy (G ⊔ L) x) ∧
      (∀ g ∈ G, ∀ Φ Ψ : (x : X) → GermGroup (H := H) x, ∀ x ∈ rightOrbit G o,
        germAction L g (Φ * Ψ) x = germAction L g Φ x * germAction L g Ψ x) ∧
      (∀ Φ : (x : X) → GermGroup (H := H) x, ∀ x ∈ rightOrbit G o, germAction L 1 Φ x = Φ x) ∧
      ∀ g₁ ∈ G, ∀ g₂ ∈ G, ∀ Φ : (x : X) → GermGroup (H := H) x, ∀ x ∈ rightOrbit G o,
        germAction L (g₁ * g₂) Φ x = germAction L g₁ (germAction L g₂ Φ) x := by
  sorry

end ErschlerZheng
