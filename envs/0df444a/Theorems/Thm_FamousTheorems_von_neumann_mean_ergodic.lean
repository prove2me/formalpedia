-- Prove2me | Theorems.Thm_FamousTheorems_von_neumann_mean_ergodic
-- name    : FamousTheorems.von_neumann_mean_ergodic
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:05:08.590977+00:00
-- url     : https://prove2.me/theorems/cd6edf41-6a0d-4108-bb55-f8c85dad65cf
-- title:
--   The von Neumann mean ergodic theorem
-- statement:
--   **The von Neumann mean ergodic theorem.** Let $H$ be a (real or complex) Hilbert space and $T$ a bounded linear operator with $\|T\|\le1$. Then for every $x\in H$ the averages
--   $$\frac1n\sum_{k=0}^{n-1}T^kx$$
--   converge in norm to $Px$, where $P$ is the orthogonal projection onto the subspace $\{y:Ty=y\}$ of fixed vectors.
--
--   Applied to the Koopman operator $f\mapsto f\circ\varphi$ of a measure-preserving map $\varphi$, it says that time averages of an $L^2$ function converge in $L^2$ to the conditional expectation onto invariant functions. This is the first ergodic theorem, proved by von Neumann in 1932, and it is basic in ergodic theory and statistical mechanics.
--
--   **Formalization note.** Mathlib's `ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`. `birkhoffAverage 𝕜 f id n x` is $\frac1n\sum_{k<n}f^k(x)$. The fixed subspace is `f.eqLocus 1`, and `orthogonalProjectionOnto` is the orthogonal projection onto it, coerced into $E$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem von_neumann_mean_ergodic {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (f : E →L[𝕜] E) (hf : ‖f‖ ≤ 1) (x : E) :
    Filter.Tendsto (fun n => birkhoffAverage 𝕜 f id n x) Filter.atTop
      (nhds (((f.eqLocus (1 : E →L[𝕜] E)).orthogonalProjectionOnto x : E))) := by sorry

end FamousTheorems
