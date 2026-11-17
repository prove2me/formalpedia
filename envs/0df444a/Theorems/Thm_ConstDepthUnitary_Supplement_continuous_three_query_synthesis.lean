-- Prove2me | Theorems.Thm_ConstDepthUnitary_Supplement_continuous_three_query_synthesis
-- name    : ConstDepthUnitary.Supplement.continuous_three_query_synthesis
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:23:55.150208+00:00
-- url     : https://prove2.me/theorems/edf9ffc5-88be-4360-9b8f-bccfe62171b1
-- title:
--   Theorem 4.1 — continuous three-query unitary synthesis, $S = i\,E^\dagger Q_S\mathcal F Q_S\mathcal F Q_S E$
-- statement:
--   Let $N\ge0$ and let $S\in U(N)$ be a **traceless real symmetric unitary**: $S$ is a real $N\times N$ matrix with $S^T=S$, $S^2=I$ and $\operatorname{tr}S=0$. Let $E:\mathbb C^N\to L^2(\mathbb R^N)$ be the encoding isometry onto the single-excitation states $\psi_x(v)=\sqrt{2/\pi^{N/2}}\,e^{-\|v\|_2^2/2}\,v_x$, let $Q_S$ be the quadratic-phase oracle $(Q_S\psi)(v)=e^{\frac12 i\,v^TSv}\psi(v)$, and let $\mathcal F$ be the Fourier transform
--   $$
--   (\mathcal F\psi)(w)=\frac{1}{(2\pi)^{N/2}}\int_{\mathbb R^N}e^{-i\,u^Tw}\,\psi(u)\,du .
--   $$
--   Then the following is an exact identity of operators on $\mathbb C^N$:
--   $$
--   S=i\,E^\dagger\,Q_S\,\mathcal F\,Q_S\,\mathcal F\,Q_S\,E .
--   $$
--   That is, for every $c\in\mathbb C^N$, $\;Sc=i\,E^\dagger\big(Q_S\,\mathcal F\,Q_S\,\mathcal F\,Q_S\,Ec\big)$.
--
--   Encoding a vector in the single-excitation sector, alternating three queries to the quadratic-phase oracle with two Fourier transforms and decoding recovers the target unitary exactly. Section 5 of the paper discretizes this identity to the approximate finite algorithm of Theorem 5.1, which drives the shallow-circuit construction. By Lemma 3.1 the restriction to traceless real symmetric unitaries loses no generality.
--
--   **Formalization Note** $\mathbb R^N$ is `EuclideanSpace ℝ (Fin N)` with Lebesgue measure. $\mathcal F$ is the published `ConstDepthUnitary.contF` (a Bochner integral), not Mathlib's `𝓕`. Every function it is applied to in the identity is a Schwartz function, so it agrees there with the unitary Fourier transform on $L^2$. $E^\dagger$ is the $L^2$ pairing with the $\psi_y$. The real matrix $S$ is cast to $\mathbb C$.
--
--   Differences from the source:
--   - encoding: "S ∈ U(N) a traceless real symmetric unitary" → S a real matrix with IsTRS S (Sᵀ = S, S·S = 1, tr S = 0), cast to ℂ; reason: for real symmetric S, unitary ⇔ S² = I; same instances
--   - encoding: operators ℱ on L²(ℝ^N) and E† as an adjoint → the integral formulas (27) and ⟨ψ_y, ·⟩ as Bochner integrals on functions EuclideanSpace ℝ (Fin N) → ℂ; reason: every function they are applied to here is Schwartz, where the integrals are the L² operators
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Theorem 4.1, Eq. (28), p.20; Eqs. (21), (24), (26), (27), pp.18–20

import Mathlib
import Definitions.Def_ConstDepthUnitary_contF
import Definitions.Def_ConstDepthUnitary_IsTRS
import Definitions.Def_ConstDepthUnitary_Supplement_quadPhase
import Definitions.Def_ConstDepthUnitary_Supplement_encode
import Definitions.Def_ConstDepthUnitary_Supplement_decode

namespace ConstDepthUnitary

namespace Supplement

/-- **Theorem 4.1 (Continuous Three-Query Unitary Synthesis).** For every traceless real symmetric unitary
`S ∈ U(N)`, the exact identity `S = i E† Q_S ℱ Q_S ℱ Q_S E` holds on `ℂ^N`: for every `c ∈ ℂ^N`,
`S c = i · E†(Q_S(ℱ(Q_S(ℱ(Q_S(E c))))))`.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Theorem 4.1, Eq. (28), p.20.

**Formalization Note** `ℱ` is the published `contF`, `(ℱψ)(w) = (2π)^{−N/2} ∫ e^{−i uᵀw} ψ(u) du` (Eq. (27)),
not Mathlib's `𝓕`. Every function it is applied to here is a Schwartz function, so the integral is the
unitary `ℱ` on `L²`. "Traceless real symmetric unitary" is `IsTRS S` (`Sᵀ = S`, `S² = I`, `tr S = 0`) with
`S` real, cast to `ℂ`. Operators act right to left: `E` first, `E†` last. -/
theorem continuous_three_query_synthesis (N : ℕ) (S : Matrix (Fin N) (Fin N) ℝ) (hS : IsTRS S)
    (c : Fin N → ℂ) :
    (S.map Complex.ofReal).mulVec c =
      Complex.I • decode (quadPhase S (contF (quadPhase S (contF (quadPhase S (encode c)))))) := by sorry

end Supplement

end ConstDepthUnitary
