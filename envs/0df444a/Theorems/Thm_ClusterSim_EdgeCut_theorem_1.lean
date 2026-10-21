-- Prove2me | Theorems.Thm_ClusterSim_EdgeCut_theorem_1
-- name    : ClusterSim.EdgeCut.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:55:26.249574+00:00
-- url     : https://prove2.me/theorems/53bdba2e-9b49-4ce8-a0a5-5811737996b9
-- title:
--   Theorem 1 — a (K, d)-clustered network is estimated to precision ε with probability ≥ 2/3 from N = ⌈4·2^{4K}/ε²⌉ samples, each running r d-qubit pieces
-- statement:
--   Let $(G,\mathcal A)$ be a tensor network with a $(K,d)$-clustering into $r$ clusters: exactly $K$ edges join different clusters (edges into the final observable $O_f$ not counted) and every cluster needs at most $d$ qubits. For $s\in[8]^{E_{\mathrm{cut}}}$ let $(G',\mathcal A_s)$ be the network obtained by cutting every edge of $E_{\mathrm{cut}}$ according to $s$ and $c_s=\prod_{e}c_{s_e}$. Model one run of the pieces of $(G',\mathcal A_s)$ on the quantum device by its outcome $t_s$, whose law $\mathrm{run}(s)$ is any probability law on $[-1,1]$ with mean $T(G',\mathcal A_s)$. Let $\varepsilon>0$ and
--   $$N=\Big\lceil\frac{4\cdot 2^{4K}}{\varepsilon^2}\Big\rceil .$$
--
--   1. **Precision $\varepsilon$ with probability $2/3$.** Let $x_1,\dots,x_N$ be i.i.d. samples of $8^K c_s t_s$, where $s$ is uniform on $[8]^{E_{\mathrm{cut}}}$ and $t_s\sim\mathrm{run}(s)$. Then
--   $$\Pr\Big[\,\Big|\frac1N\sum_{i=1}^N x_i-T(G,\mathcal A)\Big|<\varepsilon\,\Big]\ \ge\ \frac23 .$$
--   2. **$d$-qubit pieces.** For every $s$, the induced clustering of $(G',\mathcal A_s)$ has no edge between different clusters, and each of its $r$ clusters needs at most $d$ qubits.
--
--   Hence the value $T(G,\mathcal A)$, which equals the expected output of the quantum-classical algorithm represented by the network, is approximated to precision $\varepsilon$ with probability at least $2/3$ by $N\cdot r=O(2^{4K}r/\varepsilon^2)$ runs of a $d$-qubit device. This is the paper's first main theorem.
--
--   **Formalization Note** The paper's $O(2^{4K}r/\varepsilon^2)$ is pinned to the proof's own sample count $N=\lceil4a^2/\varepsilon^2\rceil$ with $a=2^{2K}$ (eqs. (36)–(37)), each sample running the $r$ pieces once (eq. (38)). The run-time clause $O(2^{4K}(n+m)/\varepsilon^2)$ is not formalized (there is no cost model), nor is eq. (10), $T(G,\mathcal A)=\mathbb E_yf(y)$: the device runs enter only through the laws $\mathrm{run}(s)$, exactly as in the paper's "Note that, for each $s$, $t_s\in[-1,1]$ is a random variable with expectation $T(G',\mathcal A_s)$". The $N$ samples are the coordinates of the $N$-fold product of the one-sample law. The estimate is real and $T(G,\mathcal A)$ complex; they are compared in $\mathbb C$.
-- source:
--   Peng, Harrow, Ozols & Wu, Simulating Large Quantum Circuits on a Small Quantum Computer, arXiv:1904.00102v2, p. 9, Theorem 1 (Supplemental Material §IV; stated in the Letter on p. 3), proof pp. 9–10, eqs. (31)–(38)

import Mathlib
import Definitions.Def_ClusterSim_EdgeCut_Estimator

namespace ClusterSim.EdgeCut

open MeasureTheory

/-- Theorem 1, p. 9 (stated in the Letter on p. 3), proof pp. 9–10. Let `G` be a tensor network with a
`(K, d)`-clustering into `r` clusters, and suppose that for every `s ∈ [8]^{E_cut}` running the pieces
of the cut network `(G′, A_s)` on the device yields an outcome `t_s` whose law `run s` is a
probability law on `[−1, 1]` with mean `T(G′, A_s)`. Let `0 < ε`, `N = ⌈4·2^{4K}/ε²⌉`.

(a) The average of `N` independent samples of `8^K c_s t_s` (`s` uniform on `[8]^{E_cut}`) is within
`ε` of `T(G, A)` with probability at least `2/3`.

(b) For every `s`, the induced clustering of `(G′, A_s)` has no edge between different clusters, and
each of its `r` clusters needs at most `d` qubits; so each sample runs `r` pieces on a `d`-qubit
device, `N · r` runs in total. -/
theorem theorem_1 {G : TensorNetwork} {r K d : ℕ} (P : Clustering G r) (hP : P.IsClustered K d)
    (run : (P.Ecut → Fin 8) → Measure ℝ) [∀ s, IsProbabilityMeasure (run s)]
    (hrange : ∀ s, ∀ᵐ t ∂(run s), t ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∀ s, ((∫ t, t ∂(run s) : ℝ) : ℂ) = value (cut G P.Ecut s))
    {ε : ℝ} (hε : 0 < ε) :
    (2 / 3 : ENNReal) ≤
        Measure.pi (fun _ : Fin (numSamples K ε) => sampleLaw P run)
          {x | ‖((average x : ℝ) : ℂ) - value G‖ < ε} ∧
      ∀ s : P.Ecut → Fin 8,
        (P.cutClustering s).Ecut = ∅ ∧ ∀ i, (P.cutClustering s).qubits i ≤ d := by sorry

end ClusterSim.EdgeCut
