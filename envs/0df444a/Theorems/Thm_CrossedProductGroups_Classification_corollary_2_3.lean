-- Prove2me | Theorems.Thm_CrossedProductGroups_Classification_corollary_2_3
-- name    : CrossedProductGroups.Classification.corollary_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:44.277513+00:00
-- url     : https://prove2.me/theorems/2544b2ec-3c5c-466d-85bb-f385222ad6fc
-- title:
--   Corollary 2.3, p. 14 — group morphisms H #^f_α G → H #^{f′}_{α′} G correspond bijectively to quadruples (u, r, v, s)
-- statement:
--   Let $(H, G, \alpha, f)$ and $(H, G, \alpha', f')$ be normalized crossed systems, with weak actions $\triangleright$ and $\triangleright'$. There is a bijection between
--
--   - the set of group morphisms $\psi : H \#_\alpha^f G \to H \#_{\alpha'}^{f'} G$, and
--   - the set of quadruples $(u, r, v, s)$, where $u : H \to H$, $r : G \to H$, $v : G \to G$ are maps and $s : H \to G$ is a group morphism, satisfying the five compatibility conditions
--   $$
--   \begin{aligned}
--   v(g_1)v(g_2) &= s(f(g_1,g_2))\,v(g_1g_2),\\
--   v(g)s(h) &= s(g \triangleright h)\,v(g),\\
--   u(h_1h_2) &= u(h_1)\big(s(h_1) \triangleright' u(h_2)\big) f'(s(h_1), s(h_2)),\\
--   u(g \triangleright h)\big(s(g \triangleright h) \triangleright' r(g)\big) f'\big(s(g \triangleright h), v(g)\big) &= r(g)\big(v(g) \triangleright' u(h)\big) f'(v(g), s(h)),\\
--   r(g_1)\big(v(g_1) \triangleright' r(g_2)\big) f'(v(g_1), v(g_2)) &= u(f(g_1,g_2))\big(s(f(g_1,g_2)) \triangleright' r(g_1g_2)\big) f'\big(s(f(g_1,g_2)), v(g_1g_2)\big),
--   \end{aligned}
--   $$
--
--   under which the quadruple $(u, r, v, s)$ corresponds to the morphism
--   $$
--   \psi(h, g) = \big(u(h), s(h)\big)\cdot\big(r(g), v(g)\big) = \Big(u(h)\big(s(h) \triangleright' r(g)\big) f'\big(s(h), v(g)\big),\; s(h)v(g)\Big).
--   $$
--   Moreover every such quadruple has $u(1) = 1$, $v(1) = 1$ and $r(1) = 1$.
--
--   This describes all morphisms between two crossed products by explicit data; Proposition 3.4 specializes it to the morphisms of $\mathcal{E}_2(H, G)$.
--
--   **Formalization Note.** The bijection is an `Equiv` between the subtype of maps `ψ : H × G → H × G` preserving the two multiplications and the subtype of quadruples satisfying `IsMorphismQuadruple`; its inverse is pinned to the displayed formula, so the statement asserts the paper's correspondence and not only an equality of cardinalities. On p. 14 the sentence before the corollary writes $\alpha(g)(h) = g \triangleright' h$; it means $\alpha'$.
-- source:
--   Agore & Militaru, Crossed product of groups. Applications, arXiv:0805.4077v2, p. 14, Corollary 2.3

import Mathlib
import Definitions.Def_CrossedProductGroups_Classification_CrossedSystem
import Definitions.Def_CrossedProductGroups_Classification_E2

namespace CrossedProductGroups.Classification

theorem corollary_2_3 {H G : Type*} [Group H] [Group G]
    (α : G → MulAut H) (f : G → G → H) (hc : IsCrossedSystem α f) (hn : f 1 1 = 1)
    (α' : G → MulAut H) (f' : G → G → H) (hc' : IsCrossedSystem α' f') (hn' : f' 1 1 = 1) :
    ∃ e : {ψ : H × G → H × G // IsCrossedHom α f α' f' ψ} ≃
        {q : (H → H) × (G → H) × (G → G) × (H →* G) //
          IsMorphismQuadruple α f α' f' q.1 q.2.1 q.2.2.1 q.2.2.2},
      (∀ (u : H → H) (r : G → H) (v : G → G) (s : H →* G)
          (hq : IsMorphismQuadruple α f α' f' u r v s),
        (e.symm ⟨(u, r, v, s), hq⟩).1 =
          fun x : H × G => (u x.1 * α' (s x.1) (r x.2) * f' (s x.1) (v x.2), s x.1 * v x.2)) ∧
      ∀ (u : H → H) (r : G → H) (v : G → G) (s : H →* G),
        IsMorphismQuadruple α f α' f' u r v s → u 1 = 1 ∧ v 1 = 1 ∧ r 1 = 1 := by sorry

end CrossedProductGroups.Classification
