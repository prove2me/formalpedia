-- Prove2me | Theorems.Thm_DuistermaatKolkDistributions_tagged_quadrature
-- name    : DuistermaatKolkDistributions.tagged_quadrature
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-16T01:56:07.264139+00:00
-- url     : https://prove2.me/theorems/8fab6d6b-1bc7-4f44-8b82-35ec21943a00
-- title:
--   Agreement with tagged box quadrature
-- statement:
--   At every rational frequency and for every certified real compact smooth test, the iterated cosine and sine integrals equal the corresponding tagged box integrals.
-- source:
--   Duistermaat and Kolk, Distributions: Theory and Applications (2010), Chapter 14, pp. 177–220, https://doi.org/10.1007/978-0-8176-4675-2_14. Adapted to the represented Fourier evaluator and its integration contract.

import Definitions.Def_liuyao_ca_fd889115_k1_Distributions_FourierMission

theorem DuistermaatKolkDistributions.tagged_quadrature : ComputableDistributions.CompactFourier.TaggedQuadratureAgreementTarget := by sorry
