-- Prove2me | Theorems.Thm_EJASpectral_RootDet_nn_compatibility_reduction
-- name    : EJASpectral.RootDet.nn_compatibility_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:10.951917+00:00
-- url     : https://prove2.me/theorems/c19164b0-6c9e-452e-9504-acc7340dbe48
-- title:
--   Proof of Proposition 7.1, pp. 24–25 — (i) ζ C³, (ii) concave, (iii) (103) ⇒ Γ is a (1 + d)-LHSCB (Nesterov–Nemirovskii Prop. 5.1.7)
-- statement:
--   Let $V$ be a finite-dimensional Euclidean Jordan algebra of rank $d\ge1$, $\mathcal E = \mathbb R\times\mathcal Q$, $\zeta(u,w) = \det(w)^{1/d}-u$, $\Psi(u,w) = -\log\det(w)$ and $\Gamma = -\log\zeta + \Psi$. Suppose that
--
--   1. $\Psi$ is a $d$-LHSCB for $\mathcal E$;
--   2. $\zeta$ is $C^3$-smooth on $\operatorname{int}(\mathcal E)$;
--   3. $\zeta$ is concave on $\operatorname{int}(\mathcal E)$;
--   4. for every $\tilde u\in\operatorname{int}(\mathcal K_{\mathrm{rtdet}})$ and $\tilde p\in\mathbb R\times V$, $$\nabla^3\zeta(\tilde u)[\tilde p,\tilde p,\tilde p] \le -3\big(\nabla^2\Psi(\tilde u)[\tilde p,\tilde p]\big)^{1/2}\nabla^2\zeta(\tilde u)[\tilde p,\tilde p]. \tag{103}$$
--
--   Then $\Gamma$ is a $(1+d)$-LHSCB for $\mathcal K_{\mathrm{rtdet}}$.
--
--   This is the step of the proof where conditions (i)–(iii) give $(\mathbb R_\ge,1)$-compatibility of $\zeta$ with $\Psi$ and Nesterov–Nemirovskii Proposition 5.1.7 then yields the barrier, with parameter $1$ (for $-\log$ on $\mathbb R_\ge$) plus $d$ (for $\Psi$).
--
--   **Formalization Note** The statement is the paper's application of Nesterov–Nemirovskii Proposition 5.1.7 to this cone and these functions, not the general proposition. $(\cdot)^{1/2}$ is the real square root. $d\ge1$ is added because the paper divides by $d$.
-- source:
--   Coey, Kapelevich & Vielma, Conic optimization with spectral functions on Euclidean Jordan algebras, arXiv:2103.04104v2, p. 24, proof of Proposition 7.1, (i)–(iii) and (103); p. 25, last sentence of the proof (Nesterov & Nemirovskii 1994, Proposition 5.1.7)

import Mathlib
import Definitions.Def_EJASpectral_RootDet_EJA
import Definitions.Def_EJASpectral_RootDet_LHSCB
import Definitions.Def_EJASpectral_RootDet_RootDetCone

namespace EJASpectral.RootDet

/-- Proof of Proposition 7.1, pp. 24–25 (Nesterov–Nemirovskii Proposition 5.1.7 for this cone):
if `Ψ` is a `d`-LHSCB for `E`, `ζ` is (i) `C³` and (ii) concave on `int E`, and (iii) (103) holds on
`int K_rtdet`, then `Γ` is a `(1 + d)`-LHSCB for `K_rtdet`. -/
theorem nn_compatibility_reduction {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {d : ℕ} (hd : 0 < d) (J : EJA V d)
    (hΨ : IsLHSCB (E J) (Psi J) (d : ℝ))
    (h_smooth : ContDiffOn ℝ 3 (zeta J) (interior (E J)))
    (h_concave : ConcaveOn ℝ (interior (E J)) (zeta J))
    (h_compat : ∀ x ∈ interior (Krtdet J), ∀ h : ℝ × V,
      iteratedFDeriv ℝ 3 (zeta J) x (fun _ => h) ≤
        -3 * Real.sqrt (iteratedFDeriv ℝ 2 (Psi J) x (fun _ => h)) *
          iteratedFDeriv ℝ 2 (zeta J) x (fun _ => h)) :
    IsLHSCB (Krtdet J) (Gamma J) (1 + (d : ℝ)) := by sorry

end EJASpectral.RootDet
