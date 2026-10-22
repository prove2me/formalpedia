-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_radial_transversality
-- name    : BirkhoffGlobalSection.left_negative_closure_radial_transversality
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T20:22:21.604426+00:00
-- url     : https://prove2.me/theorems/31f001f5-a648-4529-8d76-ad9b7af07b9a
-- title:
--   Radial transversality of the subcritical Levi-Civita energy hypersurface
-- statement:
--   This is the transversality form of the star-shapedness of the Levi-Civita regularized energy hypersurface in the planar circular restricted three-body problem.
--
--   Fix a mass ratio $0<\mu<1$ and a Jacobi energy level $-c$ lying below the first critical value of the Jacobi Hamiltonian. Write a point of $\mathbb R^4$ as $s=(z,w)$ with $z=(z_1,z_2)$ and $w=(w_1,w_2)$, and let $K_{\mu,c}$ be the Levi-Civita regularized Hamiltonian
--   $$
--   K_{\mu,c}(z,w)=\frac{|w|^2}{2}+c|z|^2-\frac{1-\mu}{2}+2|z|^2(z_1w_2-z_2w_1)-\mu(z_1w_2+z_2w_1)-\frac{\mu|z|^2}{|2z^2-1|},
--   $$
--   where $z^2$ is the complex square and $|2z^2-1|$ is the distance to the regularized second collision. Let $\Omega$ be the connected component containing the origin of the open set $\{K_{\mu,c}<0,\ 2z^2\neq 1\}$, and let $\overline\Omega$ be its closure. The bounded regularized energy hypersurface is $\Sigma_{\mu,c}=\overline\Omega\cap\{K_{\mu,c}=0\}$.
--
--   For every $s\in\Sigma_{\mu,c}$, the radial derivative of $K_{\mu,c}$ is strictly positive:
--   $$
--   \frac{d}{da}\Big|_{a=1}K_{\mu,c}(a\,s)=dK_{\mu,c}(s)[s]>0.
--   $$
--
--   Equivalently, the Liouville vector field $\tfrac12(z\,\partial_z+w\,\partial_w)$ is positively transverse to $\Sigma_{\mu,c}$. This is the analytic content of the statement that $\Sigma_{\mu,c}$ is star-shaped with respect to the origin, and hence of contact type and diffeomorphic to $S^3$. It is the ingredient needed to show that the inner negative-energy region is radially star-shaped.
--
--   **Formalization Note** Lean's `deriv` returns $0$ at points of non-differentiability, so strict positivity of `deriv` also asserts that the radial energy function is differentiable at $a=1$. The hypersurface $\Sigma_{\mu,c}$ is described as the zero set of the regularized Hamiltonian inside the closure of the origin component of `{u | leviCivitaHamiltonian μ c u < 0 ∧ 0 < secondCollisionDistanceSq u}`. The subcritical hypothesis is `belowFirstCriticalValue μ c`.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4 (star-shapedness of the Levi-Civita regularized hypersurface Sigma_{mu,c} for -c below the smallest critical value), citing Frauenfelder--van Koert, The Restricted Three-Body Problem and Holomorphic Curves (2018), Lemma 4.2.1.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem left_negative_closure_radial_transversality (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ s ∈ closure
      (connectedComponentIn
        {u : Phase | leviCivitaHamiltonian μ c u < 0 ∧
          0 < secondCollisionDistanceSq u}
        (fun _ : Fin 4 => (0 : ℝ))),
      leviCivitaHamiltonian μ c s = 0 →
        0 < deriv (fun a : ℝ =>
          leviCivitaHamiltonian μ c (fun i : Fin 4 => a * s i)) 1 := by sorry

end BirkhoffGlobalSection
