-- Prove2me | Theorems.Thm_DeepONetError_universal_approximation
-- name    : DeepONetError.universal_approximation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:23:36.656596+00:00
-- url     : https://prove2.me/theorems/a56ebf3d-7428-4134-b518-10edf628e2dd
-- title:
--   Theorem 3.1: universal approximation by DeepONets
-- statement:
--   Let $D\subset\mathbb{R}^d$ be compact and nonempty, and let $U\subset\mathbb{R}^n$ be compact. Let $\mu$ be a Borel probability measure on $C(D)$, and let $\mathcal{G}:C(D)\to L^2(U)$ be Borel measurable with $\mathcal{G}\in L^2(\mu)$, i.e. $\int_{C(D)}\|\mathcal{G}(u)\|^2_{L^2(U)}\,d\mu(u)<\infty$. Then for every $\epsilon>0$ there exist
--   1. $m,p\in\mathbb{N}$ and sensors $x_1,\dots,x_m\in D$,
--   2. a ReLU approximator network $\mathcal{A}:\mathbb{R}^m\to\mathbb{R}^p$,
--   3. a ReLU trunk network $\boldsymbol\tau=(\tau_0,\dots,\tau_p):\mathbb{R}^n\to\mathbb{R}^{p+1}$,
--
--   such that the DeepONet $\mathcal{N}(u)=\tau_0+\sum_{k=1}^p\mathcal{A}_k(u(x_1),\dots,u(x_m))\,\tau_k$ satisfies
--
--   $$\|\mathcal{G}-\mathcal{N}\|_{L^2(\mu)}=\Big(\int_{C(D)}\|\mathcal{G}(u)-\mathcal{N}(u)\|^2_{L^2(U)}\,d\mu(u)\Big)^{1/2}<\epsilon.$$
--
--   The theorem removes the continuity and compactness assumptions of the Chen–Chen universal approximation theorem, at the price of measuring the error in $L^2(\mu)$.
--
--   **Formalization Note** The paper prints $\mathcal{G}:C(D)\to L^2(D)$; the codomain is $L^2(U)$, as in the displayed conclusion. $D$ and $U$ are compact, as in Section 2.2, and $D$ is nonempty (the paper's sensors $x_j\in D$ presuppose this; for $D=\emptyset$ no sensors exist and the statement would be false). The Borel $\sigma$-algebras on $C(D)$ and $L^2(U)$ are supplied as instance arguments.
-- source:
--   Lanthaler, Mishra and Karniadakis, Error estimates for DeepOnets: A deep learning framework in infinite dimensions, arXiv:2102.09618v3 (2022), Section 3.1, Theorem 3.1, p. 9; proof in Appendix C.1, pp. 74-77

import Mathlib
import Definitions.Def_DeepONetError_Basic

open MeasureTheory

namespace DeepONetError

theorem universal_approximation {d n : ℕ} (Dset : Set (Fin d → ℝ)) [CompactSpace Dset] [Nonempty Dset]
    (U : Set (Fin n → ℝ)) (hU : IsCompact U)
    [MeasurableSpace C(Dset, ℝ)] [BorelSpace C(Dset, ℝ)] [MeasurableSpace (L2 U)] [BorelSpace (L2 U)]
    (mu : Measure C(Dset, ℝ)) [IsProbabilityMeasure mu] (G : C(Dset, ℝ) → L2 U)
    (hG : Measurable G) (hG2 : (∫⁻ u, ‖G u‖ₑ ^ 2 ∂mu) < ⊤) (eps : ℝ) (heps : 0 < eps) :
    ∃ (m p : ℕ) (_ : 1 ≤ m) (_ : 1 ≤ p) (x : Fin m → Dset) (Apx : ReLUNet m p)
      (trunk : ReLUNet n (p + 1)),
      totalErr mu G (deepONet U x Apx trunk) < ENNReal.ofReal eps := by sorry

end DeepONetError
