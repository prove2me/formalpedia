-- Prove2me | Theorems.Thm_ErschlerZheng_isSubgroup_localGermSet_and_germSubgroupoid_closed
-- name    : ErschlerZheng.isSubgroup_localGermSet_and_germSubgroupoid_closed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-05T23:19:19.780661+00:00
-- url     : https://prove2.me/theorems/662d5a52-0ea3-4e1a-b00f-448be478a114
-- title:
--   Notation 3.1 — H_x is a proper subgroup of Ĝ_x and ℋ(H_o) a sub-groupoid, and neither depends on the choices of σ ∈ L
-- statement:
--   Let a group $H$ act from the right on a topological space $X$, each map $y \mapsto y \cdot h$ continuous, and let $G, L \le H$ with $L$ an auxiliary group with trivial isotropy for $G$ (`IsAuxiliary`). Then:
--
--   1. for every $x \in X$, every $g \in G$ fixing $x$ and all $\sigma_1, \sigma_2 \in L$ with $x \cdot \sigma_1 = x \cdot \sigma_2$, the elements $\sigma_1^{-1} g \sigma_1$ and $\sigma_2^{-1} g \sigma_2$ agree on a neighbourhood of $x \cdot \sigma_1$: $(g, x)^{\sigma_1} = (g, x)^{\sigma_2}$.
--
--   Moreover, let $o \in X$ with $\hat{\mathcal G}_o$ = `isotropy (G ⊔ L) o` non-trivial, let $H_o$ be a proper subgroup of $\hat{\mathcal G}_o$, and write $H_x$ for `localGermSet G L o Ho x` and $\mathcal H$ for `germSubgroupoid G L o Ho` (the bundle's $\sigma_x$ and $\sigma$ are fixed choices). Then:
--
--   2. for every $x \in o \cdot G$ and every $\sigma \in L$ with $o \cdot \sigma = x$, the set $\{(h, x) : h \in$ `G ⊔ L`, $x \cdot h = x$, $(\sigma h \sigma^{-1}, o) \in H_o\}$, which is $H_x$ built with $\sigma$ as the choice of $\sigma_x$, is a subgroup of the germ group at $x$ properly contained in $\hat{\mathcal G}_x$;
--   3. $H_x$ at $x = o$ is $H_o$;
--   4. $H_x$ does not depend on $\sigma_x$: for $x \in o \cdot G$, any $\sigma \in L$ with $o \cdot \sigma = x$ and any $h \in$ `G ⊔ L` fixing $x$, the germ of $h$ at $x$ lies in $H_x$ if and only if $(\sigma h \sigma^{-1}, o) \in H_o$;
--   5. $\mathcal H$ does not depend on the $\sigma$ of (3.1): for $g \in G$, $x \in o \cdot G$ and any $\sigma \in L$ with $x \cdot \sigma = x \cdot g$, $(g, x) \in \mathcal H$ if and only if $(g\sigma^{-1}, x) \in H_x$;
--   6. membership in $\mathcal H$ depends only on the germ: if $(g, x) \in \mathcal H$ and $g' \in G$ agrees with $g$ on a neighbourhood of $x$, then $(g', x) \in \mathcal H$;
--   7. $(1, x) \in \mathcal H$ for every $x \in o \cdot G$;
--   8. if $(g, x) \in \mathcal H$ then $(g^{-1}, x \cdot g) \in \mathcal H$;
--   9. if $(g, x) \in \mathcal H$ and $(h, x \cdot g) \in \mathcal H$ then $(gh, x) \in \mathcal H$.
--
--   Erschler and Zheng, p. 17: “It’s easy to see that since $L$ has trivial isotropy groups, if $x \cdot \sigma_1 = x \cdot \sigma_2$ for $\sigma_1, \sigma_2 \in L$, then $(g, x)^{\sigma_1} = (g, x)^{\sigma_2}$.” and pp. 17–18, Notation 3.1: “Let $G \curvearrowright \mathcal X$ by homeomorphisms and $L$ be an auxiliary group with trivial isotropy. Suppose the isotropy group $\hat{\mathcal G}_o$ of $\hat{\mathcal G}$ is non-trivial at some point $o \in \mathcal X$. Let $H_o \lneqq \hat{\mathcal G}_o$ be a proper subgroup of $\hat{\mathcal G}_o$. For each point $x \in o \cdot G$, fix a choice of $\sigma_x \in L$ such that $o \cdot \sigma_x = x$. Let $H_x := \{(g, x) \in \hat{\mathcal G}_x : (\sigma_x g \sigma_x^{-1}, o) \in H_0\}$, then $H_x$ is a proper subgroup of $\hat{\mathcal G}_x$. Let $\mathcal H = \mathcal H(H_o)$ be the following sub-groupoid of $\mathcal G$: (3.1) $\mathcal H := \{(g, x) : g \in G,\ x \in o \cdot G,\ (g\sigma^{-1}, x) \in H_x \text{ where } \sigma \in L,\ x \cdot g = x \cdot \sigma\}$.”
--
--   ($H_0$ is $H_o$.) The notation asserts without proof that $H_x$ is a proper subgroup, for whichever $\sigma_x$ is fixed (conjunct 2), and that $\mathcal H$ is a sub-groupoid; it presupposes that the formula for $H_x$ at $x = o$ gives back $H_o$ (conjunct 3), and that neither $H_x$ nor $\mathcal H$ depends on the choice of $\sigma_x$ or of the $\sigma$ in (3.1) (conjuncts 4 and 5). The word “sub-groupoid” is spelled out as conjuncts 6–9: $\mathcal H$ is a set of germs (conjunct 6, since it is defined on pairs $(g, x)$), it contains the identity germs at the points of $o \cdot G$, where it lives, and it is closed under inverse and composition. Conjunct 1 is the sentence before the notation, which makes $H_x$ well defined; like that sentence, it assumes only that $L$ is auxiliary, with no point $o$ and no $H_o$. The hypothesis that $\hat{\mathcal G}_o$ is non-trivial is kept as printed.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), pp. 17–18, Notation 3.1

import Mathlib
import Definitions.Def_ErschlerZheng_Germs
open scoped RightActions

namespace ErschlerZheng

theorem isSubgroup_localGermSet_and_germSubgroupoid_closed {H : Type*} [Group H] {X : Type*}
    [TopologicalSpace X] [MulAction Hᵐᵒᵖ X] [ContinuousConstSMul Hᵐᵒᵖ X] (G L : Subgroup H)
    (hL : IsAuxiliary (X := X) G L) :
    (∀ x : X, ∀ g ∈ G, x <• g = x → ∀ σ₁ ∈ L, ∀ σ₂ ∈ L, x <• σ₁ = x <• σ₂ →
        GermEq (x <• σ₁) (σ₁⁻¹ * g * σ₁) (σ₂⁻¹ * g * σ₂)) ∧
    ∀ o : X, isotropy (G ⊔ L) o ≠ ⊥ → ∀ Ho : Subgroup (GermGroup (H := H) o),
      Ho < isotropy (G ⊔ L) o →
      (∀ x ∈ rightOrbit G o, ∀ σ ∈ L, o <• σ = x → ∃ K : Subgroup (GermGroup (H := H) x),
        (K : Set (GermGroup (H := H) x)) =
          {θ | ∃ h ∈ G ⊔ L, x <• h = x ∧ germ x h = θ ∧ germ o (σ * h * σ⁻¹) ∈ Ho} ∧
        K < isotropy (G ⊔ L) x) ∧
      localGermSet G L o Ho o = (Ho : Set (GermGroup (H := H) o)) ∧
      (∀ x ∈ rightOrbit G o, ∀ σ ∈ L, o <• σ = x → ∀ h ∈ G ⊔ L, x <• h = x →
        (germ x h ∈ localGermSet G L o Ho x ↔ germ o (σ * h * σ⁻¹) ∈ Ho)) ∧
      (∀ g ∈ G, ∀ x ∈ rightOrbit G o, ∀ σ ∈ L, x <• σ = x <• g →
        ((g, x) ∈ germSubgroupoid G L o Ho ↔ germ x (g * σ⁻¹) ∈ localGermSet G L o Ho x)) ∧
      (∀ g g' : H, ∀ x : X, (g, x) ∈ germSubgroupoid G L o Ho → g' ∈ G → GermEq x g g' →
        (g', x) ∈ germSubgroupoid G L o Ho) ∧
      (∀ x ∈ rightOrbit G o, ((1 : H), x) ∈ germSubgroupoid G L o Ho) ∧
      (∀ g : H, ∀ x : X, (g, x) ∈ germSubgroupoid G L o Ho →
        (g⁻¹, x <• g) ∈ germSubgroupoid G L o Ho) ∧
      ∀ g h : H, ∀ x : X, (g, x) ∈ germSubgroupoid G L o Ho →
        (h, x <• g) ∈ germSubgroupoid G L o Ho → (g * h, x) ∈ germSubgroupoid G L o Ho := by
  sorry

end ErschlerZheng
