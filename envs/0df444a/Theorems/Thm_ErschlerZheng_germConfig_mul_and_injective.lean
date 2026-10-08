-- Prove2me | Theorems.Thm_ErschlerZheng_germConfig_mul_and_injective
-- name    : ErschlerZheng.germConfig_mul_and_injective
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-05T23:46:45.811985+00:00
-- url     : https://prove2.me/theorems/a4dc4e2c-c88c-4bb7-b5bb-538b67d690a3
-- title:
--   Fact 3.5 — ϑ(g) = (Φ_g, g) is a monomorphism into 𝒲: Φ_g(x) ∈ Ĝ_x, Φ_{g₁g₂} = Φ_{g₁}·τ_{g₁}Φ_{g₂}, ϑ injective
-- statement:
--   Let a group $H$ act from the right on a topological space $X$, each map $y \mapsto y \cdot h$ continuous, let $G, L \le H$ with $L$ an auxiliary group with trivial isotropy for $G$ (`IsAuxiliary`), and let $o \in X$. Write $\Phi_g(x)$ for the germ configuration `germConfig L g x`, the germ of $g\sigma^{-1}$ at $x$ for $\sigma \in L$ with $x \cdot \sigma = x \cdot g$, and $\tau_g$ for `germAction L g`. Then:
--
--   1. for $g \in G$ and $x \in o \cdot G$, $\Phi_g(x) \in \hat{\mathcal G}_x$ (= `isotropy (G ⊔ L) x`);
--   2. for $g_1, g_2 \in G$ and $x \in o \cdot G$, $\Phi_{g_1g_2}(x) = \Phi_{g_1}(x)\,(\tau_{g_1}\Phi_{g_2})(x)$;
--   3. the map $g \mapsto \bigl((\Phi_g(x))_{x \in o \cdot G},\, g\bigr)$ is injective on $G$.
--
--   Erschler and Zheng, p. 19, Fact 3.5: “Let $\vartheta : G \to \mathcal W$ by defined as $\vartheta(g) = (\Phi_g, g)$ such that for $x \in o \cdot G$, (3.3) $\Phi_g(x) = (g\sigma^{-1}, x) \in \mathcal G_x$, where $\sigma \in L$, $x \cdot g = x \cdot \sigma$. Then $\vartheta$ is a monomorphism.”
--
--   Here $\mathcal W = \bigl(\prod_{x \in o \cdot G} \hat{\mathcal G}_x\bigr) \rtimes G$ with multiplication $(\Phi, g)(\Phi', g') = (\Phi\tau_g\Phi', gg')$ (p. 19). Conjunct 1 says that $\vartheta(g)$ lies in $\mathcal W$, conjunct 2 is $\vartheta(g_1g_2) = \vartheta(g_1)\vartheta(g_2)$ in the first coordinate (the second is $g_1g_2$ on both sides), and conjunct 3 is injectivity. Conjunct 1 asserts $\Phi_g(x) \in \hat{\mathcal G}_x$ rather than the printed $\Phi_g(x) \in \mathcal G_x$, a weaker claim since $\mathcal G_x \le \hat{\mathcal G}_x$; the printed one fails in general ([`ErschlerZheng.not_forall_germConfig_mem_isotropy`](https://prove2.me/theorems/3e371f7c-7f6c-4dd3-9bc9-a315888dd4aa)).
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 19, Fact 3.5

import Mathlib
import Definitions.Def_ErschlerZheng_Germs
open scoped RightActions

namespace ErschlerZheng

theorem germConfig_mul_and_injective {H : Type*} [Group H] {X : Type*} [TopologicalSpace X]
    [MulAction Hᵐᵒᵖ X] [ContinuousConstSMul Hᵐᵒᵖ X] (G L : Subgroup H)
    (hL : IsAuxiliary (X := X) G L) (o : X) :
    (∀ g ∈ G, ∀ x ∈ rightOrbit G o, germConfig L g x ∈ isotropy (G ⊔ L) x) ∧
      (∀ g₁ ∈ G, ∀ g₂ ∈ G, ∀ x ∈ rightOrbit G o,
        germConfig L (g₁ * g₂) x =
          germConfig L g₁ x * germAction L g₁ (germConfig L g₂) x) ∧
      Function.Injective fun g : G =>
        ((fun x : rightOrbit G o => germConfig L (g : H) (x : X)), (g : H)) := by
  sorry

end ErschlerZheng
