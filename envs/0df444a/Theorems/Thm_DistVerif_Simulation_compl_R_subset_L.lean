-- Prove2me | Theorems.Thm_DistVerif_Simulation_compl_R_subset_L
-- name    : DistVerif.Simulation.compl_R_subset_L
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:24:01.463391+00:00
-- url     : https://prove2.me/theorems/a2006416-549f-4726-95bb-bcc399f4c2b7
-- title:
--   Proof of Lemma 3.4 — $V\setminus R_{t-1}\subseteq L_{t-1}$ for $t<(d^p-1)/2$
-- statement:
--   Let $G(\Gamma,d,p)$ be the network of §3.1 with vertex set $V$ and $i$-left and $i$-right sets $L_i$, $R_i$, and let $t$ be an integer with $0<t<(d^p-1)/2$. Then
--   $$V\setminus R_{t-1}\subseteq L_{t-1}\qquad\text{and}\qquad V\setminus L_{t-1}\subseteq R_{t-1}.$$
--
--   The first inclusion is stated in the proof of Lemma 3.4 ("since $L_{t-1}$ and $R_{t-1}$ share some path vertices"); the second is its mirror image, used for equation (3.1), which the paper says "is proved in exactly the same way". Together they say that every vertex whose state Bob does not track is tracked by Alice and vice versa, so Alice can compute every message that crosses into Bob's region.
--
--   **Formalization Note** $0<t$ makes $t-1$ a genuine predecessor; at $t=1$ the inclusions concern $L_0=V\setminus\{r\}$ and $R_0=V\setminus\{s\}$.
-- source:
--   Das Sarma, Holzer, Kor, Korman, Nanongkai, Pandurangan, Peleg, Wattenhofer, Distributed Verification and Hardness of Distributed Approximation, SIAM J. Comput. 41 (2012), p. 1250, proof of Lemma 3.4, second paragraph ("for any t < (d^p − 1)/2, V \ R_{t−1} ⊆ L_{t−1}")

import Mathlib
import Definitions.Def_DistVerif_Simulation_Network

namespace DistVerif.Simulation

/-- **Proof of Lemma 3.4, second paragraph** (p. 1250). For `0 < t < (d^p - 1)/2`,
`V \ R_{t-1} ⊆ L_{t-1}`, and symmetrically (the mirror image used for (3.1))
`V \ L_{t-1} ⊆ R_{t-1}`. -/
theorem compl_R_subset_L (Γ d p t : ℕ) (ht0 : 0 < t) (ht : (t : ℝ) < ((d : ℝ) ^ p - 1) / 2) :
    (R Γ d p (t - 1))ᶜ ⊆ L Γ d p (t - 1) ∧ (L Γ d p (t - 1))ᶜ ⊆ R Γ d p (t - 1) := by sorry

end DistVerif.Simulation
