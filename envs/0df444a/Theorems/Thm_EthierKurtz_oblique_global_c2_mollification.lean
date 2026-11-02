-- Prove2me | Theorems.Thm_EthierKurtz_oblique_global_c2_mollification
-- name    : EthierKurtz.oblique_global_c2_mollification
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-02T04:28:45.205203+00:00
-- url     : https://prove2.me/theorems/83c360b5-aabb-420f-a161-411fecc3b5aa
-- title:
--   Global C^2 mollification up to the boundary of a bounded domain with outward normals
-- statement:
--   Let $\Omega\subset\mathbb R^d$ be bounded and open with an outward unit normal (a local $C^1$ defining function) at every boundary point, $0<\mu$, and let $f\in C^2(\Omega)$ have second partials $\partial_i\partial_j f$ that are $\mu$-Hoelder on the components of $\Omega\cap B$ (ComponentHolder) and gradient $Df=J$ on $\Omega$ for some $J$ continuous on $\overline\Omega$. Then for every $\eta>0$ there is $F\in C^\infty(\mathbb R^d)$ with
--   $$\sup_{\Omega}|F-f|\le\eta,\qquad \sup_\Omega\|DF-Df\|\le\eta,\qquad \sup_\Omega\|D^2F-D^2f\|\le\eta.$$
--
--   Role: supplies the smooth approximations $F_k\to f$ in $C^2(\Omega)$ from which the parent builds elements of the $\mu$-graph converging to a given element of the $\mu'$-graph.
-- source:
--   D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, https://doi.org/10.1007/978-3-642-61798-0, Section 7.2 (mollification, Lemma 7.2) together with the interior cone condition at a C^1 boundary; used in Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Theorem 1.5 and its proof (p. 369)

import Mathlib
import Definitions.Def_EthierKurtz_ComponentHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

theorem oblique_global_c2_mollification (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) (hbounded : Bornology.IsBounded Ω)
    (hopen : IsOpen Ω) (normal : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x)) (μ : ℝ) (hμ : 0 < μ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ContDiffOn ℝ 2 f Ω)
    (J : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
    (hJ : ContinuousOn J (closure Ω)) (hJf : ∀ x ∈ Ω, fderiv ℝ f x = J x)
    (hH : ∀ i j, ComponentHolder Ω μ (fun x => fderiv ℝ (fun y => fderiv ℝ f y
      (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)))
    (η : ℝ) (hη : 0 < η) :
    ∃ F : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧
      ∀ x ∈ Ω, |F x - f x| ≤ η ∧ ‖fderiv ℝ F x - fderiv ℝ f x‖ ≤ η ∧
        ‖fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ f) x‖ ≤ η := by sorry

end EthierKurtz
