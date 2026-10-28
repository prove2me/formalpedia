-- Prove2me | Theorems.Thm_ChannelRandomization_PostProc_lemma_2_pair_replacer
-- name    : ChannelRandomization.PostProc.lemma_2_pair_replacer
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:31.327822+00:00
-- url     : https://prove2.me/theorems/a03c483c-f898-4742-8063-984df6dfaa26
-- title:
--   p. 9, proof of Lemma 2 — ⟨φ, Φ_{I,σ}⟩ = Tr φ(σ)
-- statement:
--   For $\sigma\in B(H)$ let $\Phi_{I,\sigma}:B(K)\to B(H)$ be the map $a\mapsto(\mathrm{Tr}\,a)\,\sigma$. For every linear map $\phi:B(H)\to B(K)$,
--
--   $$\langle\phi,\Phi_{I,\sigma}\rangle=\mathrm{Tr}\,\phi(\sigma).$$
--
--   In particular $\langle\Omega,\Phi_{I,\sigma}\rangle=1$ for every trace-preserving $\Omega$ and every state $\sigma$. This identity is what identifies the channels $\mathcal C(\mathcal A,\mathcal B)$ as the dual section of the replacement maps $\{\Phi_{I,\sigma}\}$ (Lemma 2), and it is used in the proof of (i)⇒(iii) of Theorem 3.
--
--   **Formalization Note.** The paper states the identity for $\phi\in\mathcal L(\mathcal A,\mathcal B)$; the Lean statement holds for every $\mathbb C$-linear $\phi$ and every matrix $\sigma$, with the real part of the trace (the trace itself for Hermitian $\phi$ and Hermitian $\sigma$).
-- source:
--   Jenčová, Randomization theorems for quantum channels, arXiv:1404.3900v1, p. 9, proof of Lemma 2

import Mathlib
import Definitions.Def_ChannelRandomization_PostProc_Setting

namespace ChannelRandomization.PostProc
theorem lemma_2_pair_replacer {h k : ℕ} (φ : Map h k) (σ : Mat h) :
    pair φ (replacer σ) = (φ σ).trace.re := by sorry
end ChannelRandomization.PostProc
