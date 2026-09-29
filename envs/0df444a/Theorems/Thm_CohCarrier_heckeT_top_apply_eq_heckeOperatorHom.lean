-- Prove2me | Theorems.Thm_CohCarrier_heckeT_top_apply_eq_heckeOperatorHom
-- name    : CohCarrier.heckeT_top_apply_eq_heckeOperatorHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/7dd52af4-5468-5353-90db-8a3368b2f1c3
-- title:
--   Transfer and coset-sum Hecke operators agree at H=top
-- statement:
--   Let $N$ and $\ell$ be natural numbers with $\ell \neq 0$, and let $A$ be an additive abelian group. Here [`CohCarrier.GammaH N ⊤`](def/CohCarrier_Level.html#L133) is the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained by pushing forward along the inclusion $\Gamma_0(N) \hookrightarrow \mathrm{SL}_2(\mathbb{Z})$ the preimage of the full subgroup $\top \le (\mathbb{Z}/N)^\times$ under the determinant-type character $\gamma \mapsto d(\gamma)$ of [`CohCarrier.gamma0Units`](def/CohCarrier_Level.html#L121), and [`CohCarrier.H1 N ⊤ A`](def/CohCarrier_Level.html#L162) is the group of additive homomorphisms $\mathrm{Additive}\,\Gamma_H(N) \to A$, i.e. of group homomorphisms from that subgroup to $A$. Given $\varphi \in$ [`CohCarrier.H1 N ⊤ A`](def/CohCarrier_Level.html#L162), an additive homomorphism $\psi : \mathrm{Additive}\,\Gamma_0(N) \to A$, and the hypothesis that for every $\gamma \in \Gamma_H(N,\top)$ one has $\varphi(\gamma) = \psi(\gamma')$, where $\gamma'$ is the element of $\Gamma_0(N)$ with the same underlying matrix (via [`CohCarrier.GammaH_le_Gamma0`](def/CohCarrier_Level.html#L146)), the conclusion is that for every $\gamma \in \Gamma_H(N,\top)$ the value at $\gamma$ of [`CohCarrier.heckeT N ⊤ ℓ A φ`](def/CohCarrier_Level.html#L250) — the operator defined as the group-theoretic transfer of $\varphi$ composed with the conjugation map [`CohCarrier.conjL`](def/CohCarrier_Level.html#L228) from the subgroup [`CohCarrier.GammaHUpper N ⊤ ℓ`](def/CohCarrier_Level.html#L210) into $\Gamma_H(N,\top)$ — equals the value at $\gamma'$ of [`HeckeEis.heckeOperatorHom N ℓ A ψ`](def/Gamma0HeckeOperatorHom.html#L285), the composite of pull-back along the conjugation homomorphism [`HeckeEis.heckeConj`](def/Gamma0HeckeOperatorHom.html#L172) from [`HeckeEis.heckeUpper N ℓ`](def/Gamma0HeckeOperatorHom.html#L128) $= \{\gamma \in \Gamma_0(N) : \ell \mid b(\gamma)\}$ to $\Gamma_0(N)$ with the explicit coset-sum corestriction [`HeckeEis.coresHom`](def/Gamma0HeckeOperatorHom.html#L238).
--
--   This is the compatibility of the two formalised models of the Hecke operator at $\ell$ on first cohomology with trivial coefficients: the transfer-defined operator on $\mathrm{Hom}(\Gamma_H(N),A)$ at $H = (\mathbb{Z}/N)^\times$, and the corestriction-of-pull-back operator given by an explicit sum over cosets of $\Gamma_0(N) \cap \alpha^{-1}\Gamma_0(N)\alpha$ with $\alpha = \mathrm{diag}(1,\ell)$. It transports statements proved for the coset-sum operator on $\mathrm{Hom}(\Gamma_0(N),A)$ to the cohomological carrier, and is used by the Eichler–Shimura existence statement for [`CohCarrier.H1 N ⊤ A`](def/CohCarrier_Level.html#L162), by the rank computation for the corner submodule, and by the eigensystem criterion for `heckeT`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_heckeT_top_apply_eq_heckeOperatorHom.lean

import Definitions.Def_CohCarrier_Level
import Definitions.Def_Gamma0HeckeOperatorHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups in

theorem CohCarrier.heckeT_top_apply_eq_heckeOperatorHom (N ℓ : ℕ) [NeZero ℓ]
    (A : Type*) [AddCommGroup A]
    (φ : CohCarrier.H1 N ⊤ A) (ψ : Additive ↥(CongruenceSubgroup.Gamma0 N) →+ A)
    (hφψ : ∀ γ : ↥(CohCarrier.GammaH N ⊤),
      φ (Additive.ofMul γ) =
        ψ (Additive.ofMul ⟨(γ : SL(2, ℤ)), CohCarrier.GammaH_le_Gamma0 ⊤ γ.2⟩))
    (γ : ↥(CohCarrier.GammaH N ⊤)) :
    CohCarrier.heckeT N ⊤ ℓ A φ (Additive.ofMul γ) =
      HeckeEis.heckeOperatorHom N ℓ A ψ
        (Additive.ofMul ⟨(γ : SL(2, ℤ)), CohCarrier.GammaH_le_Gamma0 ⊤ γ.2⟩) := by sorry
